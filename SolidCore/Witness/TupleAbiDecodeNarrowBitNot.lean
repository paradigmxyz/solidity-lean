import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for a tuple destination of abi.decode whose data holds a narrow
complement.

~uint32(0xa7fb) is the uint32 value 0xffff5804, so
(uint32 a, uint64 b) = abi.decode(abi.encode(~uint32(0xa7fb), uint64(1)), (uint32, uint64))
yields (4294924292, 1). The tuple declaration and tuple assignment paths
lowered the data expression without the type environment, and the env-less
lowering of ~ produced the full-width not(x) word; the decoder rejected it as
a dirty uint32 and the call reverted. The data is now built at its source
types (as for the single-value and return forms), and the env-less ~ on a
typed narrow uintN operand is masked to its width. Covers a parameter
operand, the second component, tuple assignment, a widened operand, the
narrow checked-arithmetic panic, and a literal control.
-/

namespace SolidCore.Solidity.Witness.TupleAbiDecodeNarrowBitNot

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

/-- Solidity source of the contract below (imported AST):

    contract C {
        function declConst() external pure returns (uint32, uint64) {
            (uint32 a, uint64 b) = abi.decode(abi.encode(~uint32(0xa7fb), uint64(1)), (uint32, uint64));
            return (a, b);
        }
        function declConstSecond() external pure returns (uint64, uint32) {
            (uint64 b, uint32 a) = abi.decode(abi.encode(uint64(1), ~uint32(0xa7fb)), (uint64, uint32));
            return (b, a);
        }
        function declParam(uint32 x) external pure returns (uint32, uint64) {
            (uint32 a, uint64 b) = abi.decode(abi.encode(~x, uint64(1)), (uint32, uint64));
            return (a, b);
        }
        function assignConst() external pure returns (uint32, uint64) {
            uint32 a;
            uint64 b;
            (a, b) = abi.decode(abi.encode(~uint32(0xa7fb), uint64(1)), (uint32, uint64));
            return (a, b);
        }
        function declWidened() external pure returns (uint256) {
            (uint256 a, uint256 b) = abi.decode(abi.encode(uint256(~uint32(0xa7fb)), uint64(1)), (uint256, uint256));
            return a + b - 1;
        }
        function declNarrowOverflow(uint8 x, uint8 y) external pure returns (uint8) {
            (uint8 a, uint8 b) = abi.decode(abi.encode(x + y, uint8(1)), (uint8, uint8));
            return a + b;
        }
        function literalControl() external pure returns (uint32, uint64) {
            (uint32 a, uint64 b) = abi.decode(abi.encode(uint32(0xffff5804), uint64(1)), (uint32, uint64));
            return (a, b);
        }
    }
-/
def contract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "declConst",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 32, location := none }, { name := none, ty := Ty.uint 64, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 32, location := none }, { name := some "b", ty := Ty.uint 64, location := none }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "0xa7fb"))])), Arg.positional (Expr.call (Expr.typeName (Ty.uint 64)) [Arg.positional (Expr.literal (Literal.number "1"))])]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 32)), TupleItem.value (Expr.typeName (Ty.uint 64))])])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "declConstSecond",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 64, location := none }, { name := none, ty := Ty.uint 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "b", ty := Ty.uint 64, location := none }, { name := some "a", ty := Ty.uint 32, location := none }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.call (Expr.typeName (Ty.uint 64)) [Arg.positional (Expr.literal (Literal.number "1"))]), Arg.positional (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "0xa7fb"))]))]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 64)), TupleItem.value (Expr.typeName (Ty.uint 32))])])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "b"), TupleItem.value (Expr.ident "a")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "declParam",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 32, location := none }],
    returns := [{ name := none, ty := Ty.uint 32, location := none }, { name := none, ty := Ty.uint 64, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 32, location := none }, { name := some "b", ty := Ty.uint 64, location := none }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.unary UnaryOp.bitNot (Expr.ident "x")), Arg.positional (Expr.call (Expr.typeName (Ty.uint 64)) [Arg.positional (Expr.literal (Literal.number "1"))])]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 32)), TupleItem.value (Expr.typeName (Ty.uint 64))])])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "assignConst",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 32, location := none }, { name := none, ty := Ty.uint 64, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 32, location := none }] none, Stmt.varDecl [{ name := some "b", ty := Ty.uint 64, location := none }] none, Stmt.expr (Expr.assign (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]) AssignOp.assign (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "0xa7fb"))])), Arg.positional (Expr.call (Expr.typeName (Ty.uint 64)) [Arg.positional (Expr.literal (Literal.number "1"))])]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 32)), TupleItem.value (Expr.typeName (Ty.uint 64))])])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "declWidened",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "0xa7fb"))]))]), Arg.positional (Expr.call (Expr.typeName (Ty.uint 64)) [Arg.positional (Expr.literal (Literal.number "1"))])]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 256)), TupleItem.value (Expr.typeName (Ty.uint 256))])])), Stmt.returnValues (some (Expr.binary BinaryOp.sub (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "declNarrowOverflow",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }, { name := some "y", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.ident "y")), Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "1"))])]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 8)), TupleItem.value (Expr.typeName (Ty.uint 8))])])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "literalControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 32, location := none }, { name := none, ty := Ty.uint 64, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 32, location := none }, { name := some "b", ty := Ty.uint 64, location := none }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "0xffff5804"))]), Arg.positional (Expr.call (Expr.typeName (Ty.uint 64)) [Arg.positional (Expr.literal (Literal.number "1"))])]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 32)), TupleItem.value (Expr.typeName (Ty.uint 64))])])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

-- declConst
def decl_const : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 1024 contract "declConst" State.empty []
    0xffff5804 1

-- declConstSecond
def decl_const_second : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 1024 contract "declConstSecond" State.empty []
    1 0xffff5804

-- declParam
def decl_param : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 1024 contract "declParam" State.empty [Value.word 5]
    0xfffffffa 1

-- assignConst
def assign_const : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 1024 contract "assignConst" State.empty []
    0xffff5804 1

-- declWidened
def decl_widened : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "declWidened" State.empty []
    0xffff5804

-- declNarrowOverflow
def decl_narrow_overflow_panics : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 1024 contract "declNarrowOverflow" State.empty [Value.word 200, Value.word 100]
    0x11

-- literalControl
def literal_control : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 1024 contract "literalControl" State.empty []
    0xffff5804 1

#guard accepted
#guard ok decl_const
#guard ok decl_const_second
#guard ok decl_param
#guard ok assign_const
#guard ok decl_widened
#guard ok decl_narrow_overflow_panics
#guard ok literal_control

end SolidCore.Solidity.Witness.TupleAbiDecodeNarrowBitNot

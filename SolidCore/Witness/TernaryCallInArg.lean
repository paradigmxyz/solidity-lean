import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TERNARY-CALL-IN-ARG (#173) — a ternary holding an internal call, in a
function-call ARGUMENT position (`double(c ? one() : 2)`).

The call-argument hoister (`FunctionDecl.hoistDirectInternalCallArgsAux?` in
`SolidCore/Solidity/Interface.lean`) formerly hoisted a call-in-argument ONLY
when the argument was a DIRECT call (`Arg.directInternalCall?` matches only
`Expr.call (Expr.ident _) _`). A ternary argument fell into the `| none =>`
arm and was passed unchanged into the residual PURE argument lowering
(`Expr.toCoreAs?`), which cannot lower a ternary whose branch is a non-pure
call. The argument-list lowering then returned `none`, so the function — and
thus the whole contract's executable lowering — declined
(`TypeError.unsupported`), even though acceptance (`importedContractAccepted`)
was already `true`. solc + real EVM run `f(true) = 2`, `f(false) = 4`.

The same ternary-with-call already lowered fine as a BINARY OPERAND, a REQUIRE
CONDITION, and in a RETURN, because those positions descend into ternary
branches through `FunctionDecl.internalExprSingleReturnUseCore?` (the guarded-
branch ternary-call hoister: it binds the ternary result to a temp and hoists
each branch's inner call into the corresponding guarded arm, so the untaken
branch's call never runs). The fix routes a ternary ARGUMENT through that SAME
hoister, binding the ternary result to a temp and substituting the temp read as
the residual argument, preserving solc's left-to-right argument evaluation
order. A ternary with pure branches makes the hoister decline (`none`), so the
pure-argument path is used unchanged (no over-accept traded in).

Real-EVM Forge ground truth: `tests/forge-harness/ternary-call-in-arg` (18
tests pass under pinned solc 0.8.35 + cancun). `#eval`-confirmed runtime words
pinned with `#guard`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TernaryCallInArg

def importedSourceName : String := "tests/forge-harness/ternary-call-in-arg/src/TernaryCallInArg.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "TernaryCallInArgHarnessTarget"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "one",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "two",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "2")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "double",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.ident "x") (Expr.literal (Literal.number "2"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "combine",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "a") (Expr.literal (Literal.number "10"))) (Expr.ident "b")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callThen",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "double") [Arg.positional (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "one") []) (Expr.literal (Literal.number "2")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callElse",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "double") [Arg.positional (Expr.ternary (Expr.ident "c") (Expr.literal (Literal.number "9")) (Expr.call (Expr.ident "two") []))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callBoth",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "double") [Arg.positional (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "one") []) (Expr.call (Expr.ident "two") []))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "assignRhs",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "v", ty := Ty.uint 256, location := none }] (some (Expr.call (Expr.ident "double") [Arg.positional (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "one") []) (Expr.literal (Literal.number "2")))])), Stmt.returnValues (some (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "orderTwoArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "combine") [Arg.positional (Expr.call (Expr.ident "one") []), Arg.positional (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "two") []) (Expr.literal (Literal.number "3")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "litTernaryArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "double") [Arg.positional (Expr.ternary (Expr.ident "c") (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "2")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "binaryOperand",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "one") []) (Expr.literal (Literal.number "2"))) (Expr.literal (Literal.number "10"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "requireCond",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.gt (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "one") []) (Expr.call (Expr.ident "two") [])) (Expr.literal (Literal.number "0"))), Arg.positional (Expr.literal (Literal.string "positive"))]), Stmt.returnValues (some (Expr.literal (Literal.number "42")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "returnTernary",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "one") []) (Expr.call (Expr.ident "two") [])))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TernaryCallInArg
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TernaryCallInArg

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.TernaryCallInArg.importedContract

-- The imported contract type-checks (accepted): every ternary-call-in-argument
-- shape passes the acceptance predicate (this held even before the fix).
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TernaryCallInArg.importedContractAccepted

private def bTrue : List CoreValue := [Value.word 1]
private def bFalse : List CoreValue := [Value.word 0]

private def callWord (fn : Name) (args : List CoreValue) (expected : Word) :
    Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam fn State.empty args expected

-- DIVERGED before the fix (contract failed to lower): call in the THEN branch
-- of a ternary argument. f(true) = double(1) = 2 ; f(false) = double(2) = 4.
def callThen_true_is_2 : Except TypeError Bool := callWord "callThen" bTrue 2
def callThen_false_is_4 : Except TypeError Bool := callWord "callThen" bFalse 4

-- Call in the ELSE branch. true -> double(9) = 18 ; false -> double(2) = 4.
def callElse_true_is_18 : Except TypeError Bool := callWord "callElse" bTrue 18
def callElse_false_is_4 : Except TypeError Bool := callWord "callElse" bFalse 4

-- Call in BOTH branches. true -> double(1) = 2 ; false -> double(2) = 4.
def callBoth_true_is_2 : Except TypeError Bool := callWord "callBoth" bTrue 2
def callBoth_false_is_4 : Except TypeError Bool := callWord "callBoth" bFalse 4

-- Same shape as an assignment RHS. true -> 2 ; false -> 4.
def assignRhs_true_is_2 : Except TypeError Bool := callWord "assignRhs" bTrue 2
def assignRhs_false_is_4 : Except TypeError Bool := callWord "assignRhs" bFalse 4

-- Ternary-call in the SECOND argument; the first argument's call (`one()`) must
-- evaluate first (left-to-right). combine(a,b) = a*10+b.
-- true -> combine(1,2) = 12 ; false -> combine(1,3) = 13.
def orderTwoArg_true_is_12 : Except TypeError Bool := callWord "orderTwoArg" bTrue 12
def orderTwoArg_false_is_13 : Except TypeError Bool := callWord "orderTwoArg" bFalse 13

-- ISOLATION: already-working positions must STAY MATCHING.
-- Ternary of literals as argument (no call). true -> 2 ; false -> 4.
def litTernaryArg_true_is_2 : Except TypeError Bool := callWord "litTernaryArg" bTrue 2
def litTernaryArg_false_is_4 : Except TypeError Bool := callWord "litTernaryArg" bFalse 4
-- Ternary-call as binary operand. true -> 11 ; false -> 12.
def binaryOperand_true_is_11 : Except TypeError Bool := callWord "binaryOperand" bTrue 11
def binaryOperand_false_is_12 : Except TypeError Bool := callWord "binaryOperand" bFalse 12
-- Ternary-call as require condition (both -> 42).
def requireCond_true_is_42 : Except TypeError Bool := callWord "requireCond" bTrue 42
def requireCond_false_is_42 : Except TypeError Bool := callWord "requireCond" bFalse 42
-- Ternary-call in a return. true -> 1 ; false -> 2.
def returnTernary_true_is_1 : Except TypeError Bool := callWord "returnTernary" bTrue 1
def returnTernary_false_is_2 : Except TypeError Bool := callWord "returnTernary" bFalse 2

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted

#guard isOkTrue callThen_true_is_2
#guard isOkTrue callThen_false_is_4
#guard isOkTrue callElse_true_is_18
#guard isOkTrue callElse_false_is_4
#guard isOkTrue callBoth_true_is_2
#guard isOkTrue callBoth_false_is_4
#guard isOkTrue assignRhs_true_is_2
#guard isOkTrue assignRhs_false_is_4
#guard isOkTrue orderTwoArg_true_is_12
#guard isOkTrue orderTwoArg_false_is_13

#guard isOkTrue litTernaryArg_true_is_2
#guard isOkTrue litTernaryArg_false_is_4
#guard isOkTrue binaryOperand_true_is_11
#guard isOkTrue binaryOperand_false_is_12
#guard isOkTrue requireCond_true_is_42
#guard isOkTrue requireCond_false_is_42
#guard isOkTrue returnTernary_true_is_1
#guard isOkTrue returnTernary_false_is_2

end TernaryCallInArg
end Witness
end Solidity
end SolidCore

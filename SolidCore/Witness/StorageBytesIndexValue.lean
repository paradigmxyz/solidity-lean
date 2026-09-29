import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Storage indexing of a dynamic `bytes` value produces `bytes1`.  The interpreter
formerly returned a bare word for `data[i]`, so comparing that value with an
explicit `bytes1` reverted with a type-mismatch Panic(0).  This exact regression
crosses the short/long storage encoding boundary by pushing and reading 41 bytes.
-/

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

namespace SolidCore.Solidity.Witness.StorageBytesIndexValue


def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "c"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "data",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "test",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 8, location := none }] (some (Expr.literal (Literal.number "0"))))) (some (Expr.binary BinaryOp.le (Expr.ident "i") (Expr.literal (Literal.number "40")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.expr (Expr.call (Expr.member (Expr.ident "data") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "i") (Expr.literal (Literal.number "1")))])])), Stmt.forLoop (some (Stmt.varDecl [{ name := some "j", ty := Ty.int 8, location := none }] (some (Expr.literal (Literal.number "40"))))) (some (Expr.binary BinaryOp.ge (Expr.ident "j") (Expr.literal (Literal.number "0")))) (some (Expr.unary UnaryOp.postDecrement (Expr.ident "j"))) (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.index (Expr.ident "data") (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.ident "j")])) (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "j") (Expr.literal (Literal.number "1")))])]))])])]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end SolidCore.Solidity.Witness.StorageBytesIndexValue

namespace SolidCore.Solidity.Witness.StorageBytesIndexValue

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def reads_all_41_bytes : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1000 importedContract "test" State.empty [] 0

#guard importedContractAccepted
#guard isOkTrue reads_all_41_bytes

end SolidCore.Solidity.Witness.StorageBytesIndexValue

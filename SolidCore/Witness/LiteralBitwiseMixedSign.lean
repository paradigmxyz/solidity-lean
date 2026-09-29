import SolidCore.Solidity.Checked
namespace SolidCore
namespace Solidity
namespace Witness
namespace LiteralBitwiseMixedSign

/-! Mixed-sign rational constants remain untyped until their surrounding context selects a mobile type. -/

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.int 64, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.expr (Expr.call (Expr.ident "assert") [Arg.positional (Expr.binary BinaryOp.eq (Expr.ident "x") (Expr.binary BinaryOp.bitOr (Expr.binary BinaryOp.bitXor (Expr.binary BinaryOp.bitAnd (Expr.binary BinaryOp.add (Expr.binary BinaryOp.sub (Expr.binary BinaryOp.add (Expr.literal (Literal.number "128")) (Expr.literal (Literal.number "1"))) (Expr.literal (Literal.number "10"))) (Expr.literal (Literal.number "4"))) (Expr.unary UnaryOp.bitNot (Expr.literal (Literal.number "1")))) (Expr.binary BinaryOp.mul (Expr.unary UnaryOp.bitNot (Expr.literal (Literal.number "1"))) (Expr.literal (Literal.number "2")))) (Expr.binary BinaryOp.bitAnd (Expr.binary BinaryOp.add (Expr.binary BinaryOp.div (Expr.binary BinaryOp.mul (Expr.binary BinaryOp.mod (Expr.unary UnaryOp.neg (Expr.literal (Literal.number "15"))) (Expr.unary UnaryOp.neg (Expr.literal (Literal.number "10")))) (Expr.literal (Literal.number "20"))) (Expr.literal (Literal.number "2"))) (Expr.literal (Literal.number "13"))) (Expr.unary UnaryOp.bitNot (Expr.literal (Literal.number "3"))))))])]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end LiteralBitwiseMixedSign
end Witness
end Solidity
end SolidCore

#guard SolidCore.Solidity.Witness.LiteralBitwiseMixedSign.importedContractAccepted

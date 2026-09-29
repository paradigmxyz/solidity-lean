import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
ABI-ENCODE-NESTED-STRUCT-ARRAY — memory tuple/struct construction preserves
reference-typed fields as pointers.

`Outer memory o = Outer(xs)` formerly evaluated the tuple component with the
ordinary value evaluator. That dereferenced `xs` one level, leaving nested
`memoryRef` elements that the runtime-only-free type coercer could not inspect;
the initializer panicked before `abi.encode` ran. Tuple construction now retains
genuine memory pointers, and coercion accepts an opaque pointer only for a
reference-shaped target type. This also preserves Solidity's aliasing rule:
mutating `xs[0]` after construction is observed through `o.xs[0]`.

Pinned solc 0.8.35 / EVM results: nested struct encoding has length 128, the
alias control returns 9, and direct encoding of the same `Inner[]` stays 96.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeNestedStructArray

def importedSourceName : String := "AbiEncodeNestedStructArray.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "Inner",
    fields := [{ name := "n", ty := Ty.uint 256 }] }), (ContractItem.structDecl
  { name := "Outer",
    fields := [{ name := "xs", ty := Ty.array (Ty.user ({ segments := ["Inner"] })) (none) }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "xs", ty := Ty.array (Ty.user ({ segments := ["Inner"] })) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.user ({ segments := ["Inner"] })) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "xs") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.call (Expr.typeName (Ty.user ({ segments := ["Inner"] }))) [Arg.positional (Expr.literal (Literal.number "7"))])), Stmt.varDecl [{ name := some "o", ty := Ty.user ({ segments := ["Outer"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["Outer"] }))) [Arg.positional (Expr.ident "xs")])), Stmt.returnValues (some (Expr.member (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.ident "o")]) "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "aliases",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "xs", ty := Ty.array (Ty.user ({ segments := ["Inner"] })) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.user ({ segments := ["Inner"] })) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "xs") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.call (Expr.typeName (Ty.user ({ segments := ["Inner"] }))) [Arg.positional (Expr.literal (Literal.number "7"))])), Stmt.varDecl [{ name := some "o", ty := Ty.user ({ segments := ["Outer"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["Outer"] }))) [Arg.positional (Expr.ident "xs")])), Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "xs") (Expr.literal (Literal.number "0"))) "n") AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.member (Expr.ident "o") "xs") (Expr.literal (Literal.number "0"))) "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "direct",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "xs", ty := Ty.array (Ty.user ({ segments := ["Inner"] })) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.user ({ segments := ["Inner"] })) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "xs") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.call (Expr.typeName (Ty.user ({ segments := ["Inner"] }))) [Arg.positional (Expr.literal (Literal.number "7"))])), Stmt.returnValues (some (Expr.member (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.ident "xs")]) "length"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeNestedStructArray
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeNestedStructArray

open SolidCore.Solidity.TypeCheck
open SolidCore.Solidity.SolcAstImport.AbiEncodeNestedStructArray

private def returns (fn : String) (expected : Nat) : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 2048 importedContract fn
    SolidCore.Solidity.Source.State.empty [] expected

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool := importedContractAccepted
def nestedEncodeReturns128 : Except TypeError Bool := returns "f" 128
def structFieldAliasesArray : Except TypeError Bool := returns "aliases" 9
def directArrayEncodeStays96 : Except TypeError Bool := returns "direct" 96

#guard accepted
#guard isOkTrue nestedEncodeReturns128
#guard isOkTrue structFieldAliasesArray
#guard isOkTrue directArrayEncodeStays96

end AbiEncodeNestedStructArray
end Witness
end Solidity
end SolidCore

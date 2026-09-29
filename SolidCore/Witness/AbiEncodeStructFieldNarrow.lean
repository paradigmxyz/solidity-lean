import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A struct constructor nested in `abi.encode` is resolved to a tuple of
field-typed casts.  Narrow checked arithmetic inside a field must still run at
its operand width before the comparison and struct encoding.
-/

namespace SolidCore.Solidity.SolcAstImport.AbiEncodeStructFieldNarrowWitness

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ContractItem.structDecl
      { name := "S", fields := [{ name := "v", ty := Ty.bool }] },
     ContractItem.function
      { kind := FunctionKind.function
        name := some "f"
        visibility := some Visibility.external_
        mutability := StateMutability.pure
        params :=
          [{ name := some "a", ty := Ty.uint 8, location := none },
           { name := some "b", ty := Ty.uint 8, location := none }]
        returns :=
          [{ name := none, ty := Ty.bytes,
             location := some DataLocation.memory }]
        virtual := false
        override? := none
        modifiers := []
        body := some (Stmt.block
          [Stmt.returnValues (some
            (Expr.call (Expr.member (Expr.ident "abi") "encode")
              [Arg.positional
                (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] })))
                  [Arg.positional
                    (Expr.binary BinaryOp.gt
                      (Expr.binary BinaryOp.add (Expr.ident "a")
                        (Expr.ident "b"))
                      (Expr.literal (Literal.number "5")))])]))]) }] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end SolidCore.Solidity.SolcAstImport.AbiEncodeStructFieldNarrowWitness

namespace SolidCore.Solidity.Witness.AbiEncodeStructFieldNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeStructFieldNarrowWitness.importedContractDecl0

def overflowPanics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 100] 17

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.AbiEncodeStructFieldNarrowWitness.importedContractAccepted
#guard isOkTrue overflowPanics

end SolidCore.Solidity.Witness.AbiEncodeStructFieldNarrow

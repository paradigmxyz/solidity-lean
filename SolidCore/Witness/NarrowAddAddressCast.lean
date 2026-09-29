import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
`address(uint160(a + b))` must evaluate `a + b` at the uint8 operand width
before either explicit conversion.  Thus 200 + 100 reverts with Panic 0x11;
the conversions cannot turn the checked add into 256-bit arithmetic.
-/

namespace SolidCore.Solidity.SolcAstImport.NarrowAddAddressCastWitness

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ContractItem.function
      { kind := FunctionKind.function
        name := some "f"
        visibility := some Visibility.external_
        mutability := StateMutability.pure
        params :=
          [{ name := some "a", ty := Ty.uint 8, location := none },
           { name := some "b", ty := Ty.uint 8, location := none }]
        returns := [{ name := none, ty := Ty.uint 256, location := none }]
        virtual := false
        override? := none
        modifiers := []
        body := some (Stmt.block
          [Stmt.varDecl
            [{ name := some "z", ty := Ty.address false, location := none }]
            (some (Expr.call (Expr.typeName (Ty.address false))
              [Arg.positional
                (Expr.call (Expr.typeName (Ty.uint 160))
                  [Arg.positional
                    (Expr.binary BinaryOp.add (Expr.ident "a")
                      (Expr.ident "b"))])])),
           Stmt.returnValues (some
             (Expr.call (Expr.typeName (Ty.uint 256))
               [Arg.positional
                 (Expr.call (Expr.typeName (Ty.uint 160))
                   [Arg.positional (Expr.ident "z")])]))]) },
     ContractItem.function
      { kind := FunctionKind.function
        name := some "wide"
        visibility := some Visibility.external_
        mutability := StateMutability.pure
        params :=
          [{ name := some "a", ty := Ty.uint 8, location := none },
           { name := some "b", ty := Ty.uint 8, location := none }]
        returns := [{ name := none, ty := Ty.uint 256, location := none }]
        virtual := false
        override? := none
        modifiers := []
        body := some (Stmt.block
          [Stmt.varDecl
            [{ name := some "z", ty := Ty.address false, location := none }]
            (some (Expr.call (Expr.typeName (Ty.address false))
              [Arg.positional
                (Expr.call (Expr.typeName (Ty.uint 160))
                  [Arg.positional
                    (Expr.binary BinaryOp.add
                      (Expr.call (Expr.typeName (Ty.uint 256))
                        [Arg.positional (Expr.ident "a")])
                      (Expr.call (Expr.typeName (Ty.uint 256))
                        [Arg.positional (Expr.ident "b")]))])])),
           Stmt.returnValues (some
             (Expr.call (Expr.typeName (Ty.uint 256))
               [Arg.positional
                 (Expr.call (Expr.typeName (Ty.uint 160))
                   [Arg.positional (Expr.ident "z")])]))]) }] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end SolidCore.Solidity.SolcAstImport.NarrowAddAddressCastWitness

namespace SolidCore.Solidity.Witness.NarrowAddAddressCast

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam :=
  SolidCore.Solidity.SolcAstImport.NarrowAddAddressCastWitness.importedContractDecl0

def overflowPanics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 100] 17

def boundaryFits : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 55] 255

def explicitlyWideReturns300 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "wide" State.empty
    [Value.word 200, Value.word 100] 300

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.NarrowAddAddressCastWitness.importedContractAccepted
#guard isOkTrue overflowPanics
#guard isOkTrue boundaryFits
#guard isOkTrue explicitlyWideReturns300

end SolidCore.Solidity.Witness.NarrowAddAddressCast

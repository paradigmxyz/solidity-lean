import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
Local variables named `tx` and `block` shadow Solidity's magic globals.  Their
member accesses must therefore use ordinary struct-field checking, including
lvalue status, instead of the read-only builtin-global path.
-/

namespace SolidCore.Solidity.SolcAstImport.MagicGlobalShadowStructLocal

open SolidCore.Solidity.Source

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items :=
    [ContractItem.structDecl
      { name := "X", fields := [{ name := "origin", ty := Ty.address false }] },
     ContractItem.structDecl
      { name := "B", fields := [{ name := "timestamp", ty := Ty.uint 256 }] },
     ContractItem.function
      { kind := FunctionKind.function
        name := some "runTx"
        visibility := some Visibility.public_
        mutability := StateMutability.nonpayable
        params := []
        returns := [{ name := none, ty := Ty.uint 256, location := none }]
        virtual := false
        override? := none
        modifiers := []
        body := some (Stmt.block
          [Stmt.varDecl
            [{ name := some "tx", ty := Ty.user ({ segments := ["X"] }),
               location := some DataLocation.memory }] none,
           Stmt.expr (Expr.assign (Expr.member (Expr.ident "tx") "origin")
             AssignOp.assign
             (Expr.call (Expr.typeName (Ty.address false))
               [Arg.positional (Expr.literal (Literal.number "3"))])),
           Stmt.returnValues (some
             (Expr.call (Expr.typeName (Ty.uint 256))
               [Arg.positional
                 (Expr.call (Expr.typeName (Ty.uint 160))
                   [Arg.positional (Expr.member (Expr.ident "tx") "origin")])]))]) },
     ContractItem.function
      { kind := FunctionKind.function
        name := some "runBlock"
        visibility := some Visibility.public_
        mutability := StateMutability.nonpayable
        params := []
        returns := [{ name := none, ty := Ty.uint 256, location := none }]
        virtual := false
        override? := none
        modifiers := []
        body := some (Stmt.block
          [Stmt.varDecl
            [{ name := some "block", ty := Ty.user ({ segments := ["B"] }),
               location := some DataLocation.memory }] none,
           Stmt.expr (Expr.assign (Expr.member (Expr.ident "block") "timestamp")
             AssignOp.assign (Expr.literal (Literal.number "7"))),
           Stmt.returnValues
             (some (Expr.member (Expr.ident "block") "timestamp"))]) }] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

def callWords? (fn : String) : Option (List Word) :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match TypeCheck.CheckedProgram.callContract 1000 program "T"
          (CallTarget.name fn) State.empty [] with
      | Except.ok (CallResult.returned _ values) =>
          values.mapM (fun v => match v with | Value.word w => some w | _ => none)
      | _ => none
  | _ => none

end SolidCore.Solidity.SolcAstImport.MagicGlobalShadowStructLocal

namespace SolidCore.Solidity.Witness.MagicGlobalShadowStructLocal

open SolidCore.Solidity.SolcAstImport.MagicGlobalShadowStructLocal

def returns (fn : String) (expected : Nat) : Bool :=
  match callWords? fn with
  | some [w] => Source.wordEq w (expected : Source.Word)
  | _ => false

#guard importedContractAccepted
#guard returns "runTx" 3
#guard returns "runBlock" 7

end SolidCore.Solidity.Witness.MagicGlobalShadowStructLocal

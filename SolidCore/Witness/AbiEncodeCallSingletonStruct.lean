import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI.ENCODECALL SINGLETON STRUCT (#b0ece24b): after struct resolution, a
one-argument struct constructor is represented by an `Expr.tuple` of its
fields.  The encodeCall annotation must keep that tuple as one argument rather
than flattening its fields into the argument list.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeCallSingletonStruct

open SolidCore.Solidity.Source

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  items :=
    [ ContractItem.structDecl
        { name := "S", fields := [{ name := "n", ty := Ty.uint 256 }] }
    , ContractItem.function
        { kind := FunctionKind.function,
          name := some "g",
          visibility := some Visibility.external_,
          mutability := StateMutability.pure,
          params := [{ name := some "s", ty := Ty.user { segments := ["S"] },
                       location := some DataLocation.memory }],
          returns := [{ name := none, ty := Ty.uint 256 }],
          body := some (Stmt.block
            [Stmt.returnValues (some (Expr.member (Expr.ident "s") "n"))]) }
    , ContractItem.function
        { kind := FunctionKind.function,
          name := some "f",
          visibility := some Visibility.external_,
          mutability := StateMutability.view,
          returns := [{ name := none, ty := Ty.uint 256 }],
          body := some (Stmt.block
            [Stmt.returnValues (some
              (Expr.member
                (Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
                  [ Arg.positional (Expr.member (Expr.ident "this") "g")
                  , Arg.positional
                      (Expr.call (Expr.typeName (Ty.user { segments := ["S"] }))
                        [Arg.positional (Expr.literal (Literal.number "7"))]) ])
                "length"))]) } ] }

def importedContract : ContractDecl := importedContractDecl0
def importedContracts : List ContractDecl := [importedContractDecl0]
def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeCallSingletonStruct
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeCallSingletonStruct

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeCallSingletonStruct.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeCallSingletonStruct.importedContractAccepted

def f_returns_36 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "f" State.empty [] 36

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue f_returns_36

end AbiEncodeCallSingletonStruct
end Witness
end Solidity
end SolidCore

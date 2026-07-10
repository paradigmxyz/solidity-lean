import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
#139 ERROR-SELECTOR-COLLISION — bare error `.selector` is scoped PER CONTRACT.

Two sibling contracts each declare `error Bad` with a DIFFERENT signature and
each returns its own `Bad.selector`. The model built one GLOBAL flat
name->selector table (`sourceErrors ++ allContractErrors`); the same-name /
different-sig collision made `SelectorEnv.lookup?` return `none`, so the bare
`Bad.selector` failed to lower and the WHOLE contract could not be replayed
(over-reject). solc accepts and resolves the bare selector against the enclosing
contract's own visible errors (own + inherited + unshadowed file-level), exactly
as the type-checker does via `ErrorSigs.resolveByName env.errors`.

Fix: build the bare-selector error table from the TARGET contract's linearized
(`dispatchOrder`) errors plus unshadowed file-level errors, and add qualified
`Contract.Bad` selector keys so `Lib.Bad.selector` resolves to the declaring
scope even under a collision — mirroring the qualified FUNCTION/EVENT selector
entries (f6effeb).

Probed on pinned solc 0.8.35 legacy (deployed on anvil / read from runtime bin):
  - A.s()       = Bad(uint256) 0xa2f43130
  - B.s()       = Bad(address) 0x830c4ac2   (NOT poisoned by A's Bad)
  - B.q()       = Lib.Bad(bytes32) 0x30665c7b (qualified, declaring scope)
  - Derived.s() = inherited Bad(uint256) 0xa2f43130
  - UsesFree.s()= file-level Bad(bool) 0x381f6d34

`#eval`-confirmed booleans pinned with `#guard`; real-EVM Forge ground truth in
`tests/forge-harness/error-selector-collision`.
-/

open SolidCore.Solidity.Source
open SolidCore.Solidity

namespace SolidCore
namespace Solidity
namespace Witness
namespace ErrorSelectorCollision

private def selectorReturn (errName : Name) : FunctionDecl :=
{ kind := FunctionKind.function,
  name := some "s",
  visibility := some Visibility.public_,
  mutability := StateMutability.pure,
  params := [],
  returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
  virtual := false,
  override? := none,
  modifiers := [],
  body := some (Stmt.block
    [Stmt.returnValues (some (Expr.member (Expr.ident errName) "selector"))]) }

def freeBad : ErrorDecl :=
  { name := "Bad", params := [{ ty := Ty.bool }] }

def contractLib : ContractDecl :=
{ kind := ContractKind.library
  name := "Lib"
  abstract := false
  bases := []
  items := [ContractItem.errorDecl { name := "Bad", params := [{ ty := Ty.bytesN 32 }] }] }

def contractA : ContractDecl :=
{ kind := ContractKind.contract
  name := "A"
  abstract := false
  bases := []
  items :=
    [ ContractItem.errorDecl { name := "Bad", params := [{ ty := Ty.uint 256 }] }
    , ContractItem.function (selectorReturn "Bad") ] }

def contractB : ContractDecl :=
{ kind := ContractKind.contract
  name := "B"
  abstract := false
  bases := []
  items :=
    [ ContractItem.errorDecl { name := "Bad", params := [{ ty := Ty.address false }] }
    , ContractItem.function (selectorReturn "Bad")
    , ContractItem.function
      { kind := FunctionKind.function,
        name := some "q",
        visibility := some Visibility.public_,
        mutability := StateMutability.pure,
        params := [],
        returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
        virtual := false,
        override? := none,
        modifiers := [],
        body := some (Stmt.block
          [Stmt.returnValues (some (Expr.member
            (Expr.member (Expr.typeName (Ty.user ({ segments := ["Lib"] }))) "Bad")
            "selector"))]) } ] }

def contractBase : ContractDecl :=
{ kind := ContractKind.contract
  name := "Base"
  abstract := false
  bases := []
  items := [ContractItem.errorDecl { name := "Bad", params := [{ ty := Ty.uint 256 }] }] }

def contractDerived : ContractDecl :=
{ kind := ContractKind.contract
  name := "Derived"
  abstract := false
  bases := [{ base := { segments := ["Base"] }, args := [] }]
  items := [ContractItem.function (selectorReturn "Bad")] }

def contractUsesFree : ContractDecl :=
{ kind := ContractKind.contract
  name := "UsesFree"
  abstract := false
  bases := []
  items := [ContractItem.function (selectorReturn "Bad")] }

def importedSourceUnit : SourceUnit :=
  { items :=
    [ SourceItem.pragma "solidity" "^0.8.35"
    , SourceItem.freeError freeBad
    , SourceItem.contract contractLib
    , SourceItem.contract contractA
    , SourceItem.contract contractB
    , SourceItem.contract contractBase
    , SourceItem.contract contractDerived
    , SourceItem.contract contractUsesFree ] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

-- (source unit above; witnesses below)

private def selBytes (sig : String) : List SolidCore.Solidity.Source.Byte :=
  SolidCore.Solidity.Source.ABI.encodeSelector
    (SolidCore.Solidity.Source.ABI.selectorFromSignature sig)

/-- First 4 output bytes of external `fn` on contract `contractName`. -/
private def selectorOf? (contractName fn : String) :
    Option (List SolidCore.Solidity.Source.Byte) :=
  match SolidCore.Solidity.TypeCheck.CheckedInput.program importedSourceUnit with
  | Except.ok program =>
      match SolidCore.Solidity.TypeCheck.CheckedProgram.contract program contractName with
      | Except.ok c =>
          match SolidCore.Solidity.TypeCheck.CheckedContract.functionCalldata c fn [] with
          | Except.ok cd =>
              match SolidCore.Solidity.TypeCheck.CheckedContract.callCalldata 64 c
                      SolidCore.Solidity.Source.State.empty cd with
              | Except.ok r => if r.success then some (r.output.take 4) else none
              | _ => none
          | _ => none
      | _ => none
  | _ => none

-- The whole unit (free Bad + library Lib.Bad + A/B/Base/Derived/UsesFree, all
-- colliding on the name `Bad`) is ACCEPTED (formerly OVER-REJECTED).
def errorSelectorCollisionAccepted : Bool := importedContractAccepted

def aResolvesOwnBad : Bool :=
  selectorOf? "A" "s" == some (selBytes "Bad(uint256)")
def bResolvesOwnBad : Bool :=
  selectorOf? "B" "s" == some (selBytes "Bad(address)")
def siblingsDoNotPoison : Bool :=
  selectorOf? "A" "s" ≠ selectorOf? "B" "s"
def bQualifiedResolvesLibrary : Bool :=
  selectorOf? "B" "q" == some (selBytes "Bad(bytes32)")
def derivedResolvesInherited : Bool :=
  selectorOf? "Derived" "s" == some (selBytes "Bad(uint256)")
def usesFreeResolvesFileLevel : Bool :=
  selectorOf? "UsesFree" "s" == some (selBytes "Bad(bool)")

#guard errorSelectorCollisionAccepted
#guard aResolvesOwnBad
#guard bResolvesOwnBad
#guard siblingsDoNotPoison
#guard bQualifiedResolvesLibrary
#guard derivedResolvesInherited
#guard usesFreeResolvesFileLevel

end ErrorSelectorCollision
end Witness
end Solidity
end SolidCore

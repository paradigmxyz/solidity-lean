import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
EMIT-INTERFACE-EVENT-VIA-LIBRARY — an INTERFACE event emitted from inside a
LIBRARY function, called from the contract:

```solidity
interface I { event E(); }
library L {
    function f() internal { emit I.E(); }
}
contract C {
    function g() public { L.f(); }
}
```

solc+EVM `g()` => `success`, emitting exactly one `E()` log whose topic0 is
`keccak256("E()")` and whose data is empty.

solidity-lean formerly REVERTED with `Panic(0)`. The qualified emit `emit I.E()`
type-checks (`TypeContext.contractEventSig?` resolves an event declared in ANY
named type — library / interface / non-inherited contract) and lowers to the
bare event name `"E"`. But the executable event table (`ContractDecl.toCoreFromOrders?`)
only added LIBRARY events to the runtime `eventDecls` (`extraLibraryEvents`), so
an INTERFACE-declared event was absent: `Runtime.emitEvent`'s `context.eventDecl?`
lookup returned `none` and dead-ended in `RevertData.typeMismatch` = `Panic(0)`.

The fix broadens both the extra-event collection and the collision-detection set
from `allContracts.filter isLibrary` to also include interfaces
(`isLibrary d || isInterface d`), mirroring what the typecheck already accepts,
so the interface event's topic0 is soundly registered under its bare name.

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EmitInterfaceEventViaLibrary

open SolidCore.Solidity.Source

-- `interface I { event E(); }`
private def interfaceI : ContractDecl :=
  { kind := ContractKind.interface, name := "I",
    abstract := false, bases := [],
    items := [ ContractItem.eventDecl
      { name := "E", params := [], anonymous := false } ] }

-- `library L { function f() internal { emit I.E(); } }`
private def libraryL : ContractDecl :=
  { kind := ContractKind.library, name := "L",
    abstract := false, bases := [],
    items := [ ContractItem.function
      { kind := FunctionKind.function, name := some "f",
        visibility := some Visibility.internal_,
        mutability := StateMutability.nonpayable,
        params := [], returns := [],
        virtual := false, override? := none, modifiers := [],
        body := some (Stmt.block
          [ Stmt.emitEvent
              (Expr.call
                (Expr.member (Expr.typeName (Ty.user { segments := ["I"] })) "E")
                []) ]) } ] }

-- `contract C { function g() public { L.f(); } }`
private def contractC : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ ContractItem.function
      { kind := FunctionKind.function, name := some "g",
        visibility := some Visibility.public_,
        mutability := StateMutability.nonpayable,
        params := [], returns := [],
        virtual := false, override? := none, modifiers := [],
        body := some (Stmt.block
          [ Stmt.expr
              (Expr.call
                (Expr.member (Expr.typeName (Ty.user { segments := ["L"] })) "f")
                []) ]) } ] }

def importedContract : ContractDecl := contractC

def importedSourceUnit : SourceUnit :=
  { items := [ SourceItem.pragma "solidity" "^0.8.35",
               SourceItem.contract interfaceI,
               SourceItem.contract libraryL,
               SourceItem.contract contractC ] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EmitInterfaceEventViaLibrary
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EmitInterfaceEventViaLibrary

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Unit_ := SolidCore.Solidity.SolcAstImport.EmitInterfaceEventViaLibrary.importedSourceUnit

-- The whole unit (interface I + library L + contract C) is ACCEPTED.
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EmitInterfaceEventViaLibrary.importedContractAccepted

-- The divergence witness: `g()` runs to SUCCESS (pre-fix it REVERTED with
-- `Panic(0)`) and emits exactly one `E` log whose topic0 is `keccak256("E()")`
-- with empty data — matching solc+EVM.
def run_emits_interface_event : Bool :=
  match CheckedInput.callContract 64 Unit_ "C"
      (SolidCore.Solidity.Source.CallTarget.name "g")
      SolidCore.Solidity.Source.State.empty [] with
  | Except.ok (SolidCore.Solidity.Source.CallResult.returned state []) =>
      match state.events with
      | [event] =>
          event.name == "E" &&
            event.topics == [SolidCore.Solidity.Source.Keccak.digestWord "E()"] &&
            event.dataBytes == []
      | _ => false
  | _ => false

#guard accepted
#guard run_emits_interface_event

end EmitInterfaceEventViaLibrary
end Witness
end Solidity
end SolidCore

/-!
BUG#6 witnesses: LIBRARY-qualified signature rendering (solc 0.8.35-verified).

solc renders public/external LIBRARY function signatures with the parameters'
canonical SOURCE names — enums as `Lib.Mode`, structs as `Lib.S` (plus
` storage` for storage pointers), contract types by NAME — while contract
external signatures keep the external-ABI forms (`uint8`, tuple, `address`).

Pinned against `solc --hashes` + the real EVM (forge lanes
`library-qualified-selectors` / `library-enum-overloads`):
  isOff(Lib.Mode)     -> 0x02952002   (NOT isOff(uint8)    = 0xac2ecd48)
  idOf(C)             -> 0xbbf15d5e   (NOT idOf(address)   = 0xd94fe832)
  bump(Lib.S storage) -> 0x83a5a0de   (NOT bump((uint256)) = 0x2a607935)

Acceptance boundary: `library L { f(EnumA) public; f(EnumB) public }` is
solc-ACCEPTED (distinct qualified signatures), while the same pair at
CONTRACT level collides in the external ABI (both `uint8`) and is REJECTED
("Function overload clash during conversion to external types").
-/
import SolidCore.Solidity.Checked
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace LibraryQualifiedSignatures

open Solidity

private def uint256 : Ty := Solidity.Ty.uint 256

private def userTy (segments : List Name) : Ty :=
  Solidity.Ty.user { segments := segments }

private def retSeven : Solidity.Stmt :=
  Solidity.Stmt.returnValues
    (some (Solidity.Expr.literal (Solidity.Literal.number "7")))

private def publicFn (name : Name) (params : List Solidity.Parameter)
    (body : Solidity.Stmt := retSeven) : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some name
    params := params
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.nonpayable
    body := some body }

private def param (name : Name) (ty : Ty)
    (location : Option Solidity.DataLocation := none) : Solidity.Parameter :=
  { name := some name, ty := ty, location := location }

/-- `contract C { function id() public returns (uint256) { return 7; } }` -/
private def contractC : Solidity.ContractDecl :=
  { name := "C"
    items := [Solidity.ContractItem.function (publicFn "id" [])] }

/-- The audit shape:
    `library Lib { enum Mode; struct S { uint256 v; };
       isOff(Mode) public; idOf(C) public; bump(S storage) public }` -/
private def libraryLib : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "Lib"
    items :=
      [ Solidity.ContractItem.enumDecl { name := "Mode", cases := ["Off", "On"] }
      , Solidity.ContractItem.structDecl
          { name := "S", fields := [{ name := "v", ty := uint256 }] }
      , Solidity.ContractItem.function
          (publicFn "isOff" [param "m" (userTy ["Mode"])])
      , Solidity.ContractItem.function
          (publicFn "idOf" [param "c" (userTy ["C"])])
      , Solidity.ContractItem.function
          (publicFn "bump"
            [param "s" (userTy ["S"]) (some Solidity.DataLocation.storage)]
            (Solidity.Stmt.block [])) ] }

private def libSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract contractC
      , Solidity.SourceItem.contract libraryLib ] }

def libSourceAccepted : Bool := sourceUnitAccepted? libSource

/-- The LIBRARY core dispatch table answers to the pinned library-qualified
    selectors — and NOT to the external-ABI forms. -/
def libDispatchSelectorsQualified : Bool :=
  match (do
      let program ← CheckedInput.program libSource
      let lib ← CheckedProgram.contract program "Lib"
      let selectors := lib.core.functions.filterMap (fun f => f.selector?)
      Except.ok
        (selectors.contains 0x02952002 &&
          selectors.contains 0xbbf15d5e &&
          selectors.contains 0x83a5a0de &&
          !selectors.contains 0xac2ecd48 &&
          !selectors.contains 0xd94fe832 &&
          !selectors.contains 0x2a607935)) with
  | Except.ok ok => ok
  | Except.error _ => false

/-- Keccak parity of the pinned qualified signature strings themselves. -/
def pinnedSignatureHashes : Bool :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "isOff(Lib.Mode)"
      == 0x02952002 &&
    SolidCore.Solidity.Source.ABI.selectorFromSignature "idOf(C)"
      == 0xbbf15d5e &&
    SolidCore.Solidity.Source.ABI.selectorFromSignature "bump(Lib.S storage)"
      == 0x83a5a0de

private def enumOverloadItems : List Solidity.ContractItem :=
  [ Solidity.ContractItem.enumDecl { name := "EnumA", cases := ["A0", "A1"] }
  , Solidity.ContractItem.enumDecl
      { name := "EnumB", cases := ["B0", "B1", "B2"] }
  , Solidity.ContractItem.function (publicFn "f" [param "a" (userTy ["EnumA"])])
  , Solidity.ContractItem.function (publicFn "f" [param "b" (userTy ["EnumB"])]) ]

/-- `library OvLib { f(EnumA) public; f(EnumB) public }` — solc ACCEPTS. -/
private def libraryOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "OvLib"
            items := enumOverloadItems } ] }

def libraryEnumOverloadsAccepted : Bool :=
  sourceUnitAccepted? libraryOverloadSource

/-- The two library overloads get DISTINCT qualified dispatch selectors. -/
def libraryEnumOverloadSelectorsDistinct : Bool :=
  match (do
      let program ← CheckedInput.program libraryOverloadSource
      let lib ← CheckedProgram.contract program "OvLib"
      let selectors := lib.core.functions.filterMap (fun f => f.selector?)
      Except.ok
        (selectors.contains
            (SolidCore.Solidity.Source.ABI.selectorFromSignature
              "f(OvLib.EnumA)") &&
          selectors.contains
            (SolidCore.Solidity.Source.ABI.selectorFromSignature
              "f(OvLib.EnumB)"))) with
  | Except.ok ok => ok
  | Except.error _ => false

/-- The same pair at CONTRACT level still collides in the external ABI
    (both `uint8`) — REJECTED as a duplicate signature, matching solc. -/
private def contractOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CtOv", items := enumOverloadItems } ] }

def contractEnumOverloadsRejected : Bool :=
  match SourceUnit.check contractOverloadSource with
  | Except.error (TypeError.duplicateSignature _) => true
  | _ => false

#guard libSourceAccepted
#guard libDispatchSelectorsQualified
#guard pinnedSignatureHashes
#guard libraryEnumOverloadsAccepted
#guard libraryEnumOverloadSelectorsDistinct
#guard contractEnumOverloadsRejected

end LibraryQualifiedSignatures
end TypeCheck
end Solidity
end SolidCore

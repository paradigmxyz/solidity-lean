import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
OVERLOAD-MEM-VS-STORAGE (#166) — data location is part of the overload signature.

`contract C { function f(uint[] memory) ...; function f(uint[] storage) ...; }` is
ACCEPTED by solc 0.8.35: memory and storage array params are DISTINCT overload
signatures. The model REJECTED it at declaration with
`TypeError.duplicateSignature "f"`.

Root cause (SolidCore/Solidity/TypeCheck.lean): `FunctionSig.sameSignature`
compared only `name` and `params` (the `Ty` list). Both `uint[] memory` and
`uint[] storage` lower to `Ty.array (Ty.uint 256) none`, so the duplicate check
`FunctionSigs.ensureNoDuplicateSignatures` raised `duplicateSignature`.

solc's actual rule: the duplicate check uses
`FunctionType::asExternallyCallableFunction(false)` (Types.cpp), which normalizes
ONLY CallData reference params to Memory and leaves Storage as-is, then compares
location-aware via `hasEqualParameterTypes`. Net effect: memory == calldata
(duplicate), but memory != storage and calldata != storage (distinct).

The fix adds `a.paramStorageRefs == b.paramStorageRefs` to `sameSignature`.
`paramStorageRefs` is exactly `location == storage` per param (via
`Parameters.storageLocationFlags`), so memory/calldata collapse to the
non-storage bucket and storage is its own bucket — matching solc exactly.

Isolation ladder (each probed against pinned solc 0.8.35 LEGACY):
  * memStorageAccepted — f(uint[] memory) + f(uint[] storage), call f(m) => 3
      solc: ACCEPT (was over-reject). Runtime dispatch picks the memory overload.
  * memCalldataRejected — f(uint[] memory) + f(uint[] calldata)
      solc: REJECT "same name and parameter types defined twice" (memory==calldata).
  * storageCalldataAccepted — f(uint[] storage) + f(uint[] calldata)
      solc: ACCEPT (distinct).
  * singleMemoryAccepted — one f(uint[] memory)  => ACCEPT (unchanged).
  * mixedValueRefAccepted — f(uint, uint[] memory) + f(uint, uint[] storage)
      solc: ACCEPT (leading value param equal, ref param differs by location).
  * structMemStorageAccepted — struct S; f(S memory) + f(S storage) => ACCEPT.
  * identicalMemoryRejected — f(uint[] memory) twice => REJECT (true duplicate).
  * valueDuplicateRejected — f(uint) + f(uint) => REJECT (over-accept guard).

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`). The accept contract's AST is emitted by
`scripts/solc_ast_to_lean_source.py` from pinned solc 0.8.35.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace OverloadMemVsStorage

open Solidity

/-- `uint256[]` (dynamic array, no length) — the shared param element type. -/
private def arrUint : Ty := Ty.array (Ty.uint 256) none

/-- An `f` overload with a single array param at the given data location. Body
    returns `x.length` (never run for the reject/neighbor cases). -/
private def fArray (loc : DataLocation) (sm : StateMutability) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "f"
      visibility := some Visibility.internal_
      mutability := sm
      params := [{ name := some "x", ty := arrUint, location := some loc }]
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some (Stmt.block
        [Stmt.returnValues (some (Expr.member (Expr.ident "x") "length"))]) }

private def contractWith (name : String) (items : List ContractItem) : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0"
    , SourceItem.contract
        { kind := ContractKind.contract, name := name, abstract := false
          bases := [], items := items }] }

private def accepted? (unit : SourceUnit) : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit unit)

private def rejected? (unit : SourceUnit) : Bool :=
  TypeCheck.Result.isError (TypeCheck.TypecheckedInput.checkedSourceUnit unit)

-- The over-reject repro: importer-emitted AST for
--   contract C {
--     function f(uint[] memory x) internal pure returns (uint) { return x.length; }
--     function f(uint[] storage x) internal view returns (uint) { return x.length; }
--     function g() public returns (uint) { uint[] memory m = new uint[](3); return f(m); }
--   }
def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "x") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [{ name := some "x", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.storage }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "x") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "m", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.returnValues (some (Expr.call (Expr.ident "f") [Arg.positional (Expr.ident "m")]))]) })] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0",
      SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Call public `g()` (no args) against empty state; `none` on any failure. This
    EXERCISES overload resolution: only the memory overload can accept the
    `uint[] memory m`, so a returned word proves the memory overload ran. -/
def callWord? : Option SolidCore.Solidity.Source.Word :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match
          TypeCheck.CheckedProgram.callContract 1000 program "C"
            (SolidCore.Solidity.Source.CallTarget.name "g")
            SolidCore.Solidity.Source.State.empty [] with
      | Except.ok (SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word w]) => some w
      | _ => none
  | _ => none

-- Isolation-ladder neighbor source units, all built with the same vocabulary.

/-- f(uint[] memory) + f(uint[] calldata) — solc REJECTS (memory == calldata). -/
def memCalldataUnit : SourceUnit :=
  contractWith "MemCalldata"
    [ fArray DataLocation.memory StateMutability.pure
    , fArray DataLocation.calldata StateMutability.pure ]

/-- f(uint[] storage) + f(uint[] calldata) — solc ACCEPTS (distinct). -/
def storageCalldataUnit : SourceUnit :=
  contractWith "StorageCalldata"
    [ fArray DataLocation.storage StateMutability.view
    , fArray DataLocation.calldata StateMutability.pure ]

/-- single f(uint[] memory) — ACCEPT (unchanged). -/
def singleMemoryUnit : SourceUnit :=
  contractWith "SingleMemory"
    [ fArray DataLocation.memory StateMutability.pure ]

/-- two identical f(uint[] memory) — REJECT (true duplicate). -/
def identicalMemoryUnit : SourceUnit :=
  contractWith "IdenticalMemory"
    [ fArray DataLocation.memory StateMutability.pure
    , fArray DataLocation.memory StateMutability.pure ]

/-- f(uint) + f(uint) — REJECT (value-type over-accept guard). -/
def valueDuplicateUnit : SourceUnit :=
  contractWith "ValueDuplicate"
    [ (ContractItem.function
        { kind := FunctionKind.function, name := some "f"
          visibility := some Visibility.internal_
          mutability := StateMutability.pure
          params := [{ name := some "x", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false, override? := none, modifiers := []
          body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) })
    , (ContractItem.function
        { kind := FunctionKind.function, name := some "f"
          visibility := some Visibility.internal_
          mutability := StateMutability.pure
          params := [{ name := some "y", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false, override? := none, modifiers := []
          body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "y"))]) }) ]

/-- f(uint, uint[] memory) + f(uint, uint[] storage) — ACCEPT: leading value
    param is equal, the ref param differs only by (non-storage vs storage). -/
def mixedValueRefUnit : SourceUnit :=
  let mk (loc : DataLocation) (sm : StateMutability) : ContractItem :=
    ContractItem.function
      { kind := FunctionKind.function, name := some "f"
        visibility := some Visibility.internal_, mutability := sm
        params :=
          [ { name := some "n", ty := Ty.uint 256, location := none }
          , { name := some "x", ty := arrUint, location := some loc } ]
        returns := [{ name := none, ty := Ty.uint 256, location := none }]
        virtual := false, override? := none, modifiers := []
        body := some (Stmt.block
          [Stmt.returnValues (some (Expr.member (Expr.ident "x") "length"))]) }
  contractWith "MixedValueRef"
    [ mk DataLocation.memory StateMutability.pure
    , mk DataLocation.storage StateMutability.view ]

/-- struct S; f(S memory) + f(S storage) — ACCEPT (distinct). -/
def structMemStorageUnit : SourceUnit :=
  let mk (loc : DataLocation) (sm : StateMutability) : ContractItem :=
    ContractItem.function
      { kind := FunctionKind.function, name := some "f"
        visibility := some Visibility.internal_, mutability := sm
        params :=
          [ { name := some "x", ty := Ty.user { segments := ["S"] }
            , location := some loc } ]
        returns := [{ name := none, ty := Ty.uint 256, location := none }]
        virtual := false, override? := none, modifiers := []
        body := some (Stmt.block
          [Stmt.returnValues (some (Expr.member (Expr.ident "x") "s"))]) }
  contractWith "StructMemStorage"
    [ ContractItem.structDecl { name := "S", fields := [{ name := "s", ty := Ty.uint 256 }] }
    , mk DataLocation.memory StateMutability.pure
    , mk DataLocation.storage StateMutability.view ]

end OverloadMemVsStorage
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace OverloadMemVsStorage

open SolidCore.Solidity.SolcAstImport.OverloadMemVsStorage

/-- The memory/storage overload repro is ACCEPTED — the #166 over-reject closed. -/
def memStorageAccepted : Bool := importedContractAccepted

/-- Runtime dispatch: `g()` picks the memory overload and returns `m.length == 3`. -/
def memStorageDispatchesTo3 : Bool :=
  match callWord? with
  | some w => SolidCore.Solidity.Source.wordEq w (3 : SolidCore.Solidity.Source.Word)
  | none => false

/-- memory == calldata: still REJECTED (must not trade over-reject for over-accept). -/
def memCalldataRejected : Bool := rejected? memCalldataUnit

/-- storage vs calldata: distinct — ACCEPTED. -/
def storageCalldataAccepted : Bool := accepted? storageCalldataUnit

/-- single memory overload: ACCEPTED (unchanged). -/
def singleMemoryAccepted : Bool := accepted? singleMemoryUnit

/-- mixed leading value param + ref param differing by location: ACCEPTED. -/
def mixedValueRefAccepted : Bool := accepted? mixedValueRefUnit

/-- struct memory vs storage: ACCEPTED. -/
def structMemStorageAccepted : Bool := accepted? structMemStorageUnit

/-- two identical memory overloads: still REJECTED (true duplicate). -/
def identicalMemoryRejected : Bool := rejected? identicalMemoryUnit

/-- f(uint) + f(uint): still REJECTED (value-type over-accept guard). -/
def valueDuplicateRejected : Bool := rejected? valueDuplicateUnit

#guard memStorageAccepted
#guard memStorageDispatchesTo3
#guard memCalldataRejected
#guard storageCalldataAccepted
#guard singleMemoryAccepted
#guard mixedValueRefAccepted
#guard structMemStorageAccepted
#guard identicalMemoryRejected
#guard valueDuplicateRejected

end OverloadMemVsStorage
end Witness
end Solidity
end SolidCore

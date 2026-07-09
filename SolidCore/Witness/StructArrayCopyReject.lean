/-
CP1/#48 struct-array-copy-to-storage witnesses.

Named boolean checks referenced by the `struct-array-copy-legacy-reject` corpus
lane in `tests/forge-harness/manifest.json`. They pin the fix on the Lean side:

  * solc 0.8.35 LEGACY codegen REJECTS at compile time a copy INTO a storage
    array whose ELEMENT is a struct when the source is a MEMORY or CALLDATA array
    (`ArrayUtils::copyArrayToStorage`, ArrayUtils.cpp:80-84 — the
    `solUnimplementedAssert(baseType->isValueType() || !fromMemoryOrCalldata, ...)`).
    Because the corpus pins legacy, such a program is NOT ground truth; the
    typechecker must reject it (was an over-accept). Pinned by the `*Rejected`
    witnesses below (each source unit typechecks to `false`).

  * The precision boundary: the reject keys on the IMMEDIATE element being a
    struct and the source being memory/calldata. `string[]`/`uint256[][]`
    (element not a struct), `S[][]` (element is an array — solc's sibling branch
    accepts a memory source), the top-level struct assignment (`S memory ->
    S storage`, not an array-of-struct), and a storage->storage copy (source not
    memory/calldata) all stay ACCEPTED. Pinned by the `*Accepted` witnesses.

Kept in the built library so `lake build SolidCore` regression-guards them.
-/
import SolidCore.Solidity.Checked

namespace SolidCore
namespace Solidity
namespace Executable
namespace StructArrayCopy

open Solidity

private def sPath : Path := { segments := ["S"] }
private def sTy : Ty := Ty.user sPath

-- struct S { uint256 a; }
private def structS : ContractItem :=
  ContractItem.structDecl
    { name := "S", fields := [{ name := "a", ty := Ty.uint 256 }] }

private def stateVar (name : Name) (ty : Ty) : ContractItem :=
  ContractItem.stateVar
    { name := name
      ty := ty
      visibility := some Visibility.internal_
      mutability := VarMutability.mutable
      override? := none
      init := none }

-- function f(<param>) { d = <rhs> }
private def copyFn (param : Parameter) (rhs : Expr)
    (visibility : Visibility := Visibility.public_) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "f"
      visibility := some visibility
      mutability := StateMutability.nonpayable
      params := [param]
      returns := []
      virtual := false
      override? := none
      modifiers := []
      body := some (Stmt.block
        [Stmt.expr (Expr.assign (Expr.ident "d") AssignOp.assign rhs)]) }

private def memParam (ty : Ty) : Parameter :=
  { name := some "m", ty := ty, location := some DataLocation.memory }

private def cdParam (ty : Ty) : Parameter :=
  { name := some "m", ty := ty, location := some DataLocation.calldata }

private def unit (items : List ContractItem) : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.contract
          { kind := ContractKind.contract
            name := "C"
            abstract := false
            bases := []
            items := items } ] }

private def accepted? (u : SourceUnit) : Bool :=
  TypeCheck.sourceUnitAccepted? u

-- ===== REJECTS: a memory/calldata array of struct into a storage array. =====

-- S[] d; f(S[] memory m) { d = m; }
def dynStructMemRejected : Bool :=
  accepted? (unit
    [structS, stateVar "d" (Ty.array sTy none),
      copyFn (memParam (Ty.array sTy none)) (Expr.ident "m")]) == false

-- S[] d; f(S[2] memory m) { d = m; }  (fixed source, still rejected)
def fixedStructMemRejected : Bool :=
  accepted? (unit
    [structS, stateVar "d" (Ty.array sTy none),
      copyFn (memParam (Ty.array sTy (some 2))) (Expr.ident "m")]) == false

-- S[] d; f(S[] calldata m) external { d = m; }
def structCalldataRejected : Bool :=
  accepted? (unit
    [structS, stateVar "d" (Ty.array sTy none),
      copyFn (cdParam (Ty.array sTy none)) (Expr.ident "m")
        Visibility.external_]) == false

-- ===== ACCEPTS: precision boundary — none of these may over-reject. =====

-- string[] d; f(string[] memory m) { d = m; }  (element is not a struct)
def stringArrMemAccepted : Bool :=
  accepted? (unit
    [stateVar "d" (Ty.array Ty.string none),
      copyFn (memParam (Ty.array Ty.string none)) (Expr.ident "m")]) == true

-- uint256[][] d; f(uint256[][] memory m) { d = m; }  (element is uint256[])
def uintNestedMemAccepted : Bool :=
  let ta := Ty.array (Ty.array (Ty.uint 256) none) none
  accepted? (unit
    [stateVar "d" ta, copyFn (memParam ta) (Expr.ident "m")]) == true

-- S[][] d; f(S[][] memory m) { d = m; }  (element is S[] — an array, not a struct)
def nestedStructMemAccepted : Bool :=
  let ta := Ty.array (Ty.array sTy none) none
  accepted? (unit
    [structS, stateVar "d" ta, copyFn (memParam ta) (Expr.ident "m")]) == true

-- S d; f(S memory m) { d = m; }  (top-level struct, not an array-of-struct)
def topLevelStructAccepted : Bool :=
  accepted? (unit
    [structS, stateVar "d" sTy,
      copyFn (memParam sTy) (Expr.ident "m")]) == true

-- S[] d; S[] e; f() { d = e; }  (storage -> storage; source not memory/calldata)
def storageToStorageAccepted : Bool :=
  let ta := Ty.array sTy none
  accepted? (unit
    [ structS, stateVar "d" ta, stateVar "e" ta
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "f"
          visibility := some Visibility.public_
          mutability := StateMutability.nonpayable
          params := []
          returns := []
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [Stmt.expr
              (Expr.assign (Expr.ident "d") AssignOp.assign (Expr.ident "e"))]) } ])
    == true

end StructArrayCopy
end Executable
end Solidity
end SolidCore

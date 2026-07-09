/-
#63 (GET-STRUCT) struct public-getter member-omission witnesses.

Named boolean checks referenced by the `getter-struct-reject` corpus lane in
`tests/forge-harness/manifest.json`. They pin the fix that made solidity-lean's
STRUCT public-getter member-omission rule SHALLOW, matching solc 0.8.35.

solc ground truth (`FunctionType::FunctionType(VariableDeclaration const&)`,
Types.cpp:2868, member skip at ~2898-2915): when building a struct getter's
return tuple, solc omits ONLY a *direct* mapping member and a *direct*
(non-string/bytes) array member of the gettered struct. A nested STRUCT member
is returned WHOLE (not recursed into). The two getter-level rejections live in
TypeChecker.cpp:548-556:

  * error 6744 "Internal or recursive type is not allowed for public state
    variables." — a returned member (now that nested structs are returned whole)
    transitively contains a mapping, so the getter has no external interface
    type. Pinned by `nestedMappingGetterRejected`.

  * error 5359 "The struct has all its members omitted, therefore the getter
    cannot return any values." — every member of the gettered struct is omitted
    (all mappings/arrays), so the getter returns nothing. Pinned by
    `allMembersOmittedRejected`.

The precision boundary (must NOT over-reject): a nested struct whose members are
all value/array types is returned whole and stays ACCEPTED, top-level omission
of mapping+array while keeping value/string members stays ACCEPTED. Pinned by
the `*Accepted` witnesses (each source unit typechecks to `true`).

Kept in the built library so `lake build SolidCore` regression-guards them.
-/
import SolidCore.Solidity.Checked

namespace SolidCore
namespace Solidity
namespace Executable
namespace GetterStructReject

open Solidity

private def uintTy : Ty := Ty.uint 256
private def mapTy : Ty := Ty.mapping uintTy uintTy
private def arrTy : Ty := Ty.array uintTy none

private def uPath (s : String) : Ty := Ty.user { segments := [s] }

private def pubVar (name : Name) (ty : Ty) : ContractItem :=
  ContractItem.stateVar
    { name := name
      ty := ty
      visibility := some Visibility.public_
      mutability := VarMutability.mutable
      override? := none
      init := none }

private def sdecl (name : Name) (fs : List (Name × Ty)) : ContractItem :=
  ContractItem.structDecl
    { name := name, fields := fs.map (fun (n, t) => { name := n, ty := t }) }

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

-- ===== REJECTS =====

-- solc 6744: a nested struct member (returned whole) transitively contains a
-- mapping.
--   struct Inner { uint a; mapping(uint=>uint) m; }
--   struct Outer { uint x; Inner inner; }
--   Outer public o;
def nestedMappingGetterRejected : Bool :=
  accepted? (unit
    [ sdecl "Inner" [("a", uintTy), ("m", mapTy)]
    , sdecl "Outer" [("x", uintTy), ("inner", uPath "Inner")]
    , pubVar "o" (uPath "Outer") ]) == false

-- solc 5359: every direct member is omitted (mapping + array).
--   struct S { mapping(uint=>uint) m; uint[] arr; }
--   S public s;
def allMembersOmittedRejected : Bool :=
  accepted? (unit
    [ sdecl "S" [("m", mapTy), ("arr", arrTy)]
    , pubVar "s" (uPath "S") ]) == false

-- ===== ACCEPTS: precision boundary — none of these may over-reject. =====

-- The #1 shape: nested struct member containing an ARRAY is returned WHOLE.
--   struct Inner { uint a; uint[] arr; }
--   struct Outer { uint x; Inner inner; }
--   Outer public o;   ->   o() returns (uint x, (uint a, uint[] arr) inner)
def nestedArrayStructAccepted : Bool :=
  accepted? (unit
    [ sdecl "Inner" [("a", uintTy), ("arr", arrTy)]
    , sdecl "Outer" [("x", uintTy), ("inner", uPath "Inner")]
    , pubVar "o" (uPath "Outer") ]) == true

-- Nested struct of pure value members is returned whole.
--   struct Inner { uint a; uint b; }
--   struct Outer { uint x; Inner inner; }
--   Outer public o;   ->   o() returns (uint x, (uint a, uint b) inner)
def nestedValueStructAccepted : Bool :=
  accepted? (unit
    [ sdecl "Inner" [("a", uintTy), ("b", uintTy)]
    , sdecl "Outer" [("x", uintTy), ("inner", uPath "Inner")]
    , pubVar "o" (uPath "Outer") ]) == true

-- Top-level omission: drop a *direct* mapping + array, keep value/string
-- members, and return a nested pure-value struct whole.
--   struct Inner { uint a; uint b; }
--   struct S { uint keep; string label; mapping(uint=>uint) m; uint[] dropped;
--              Inner inner; }
--   S public s;  ->  s() returns (uint keep, string label, (uint a, uint b) inner)
def topLevelOmissionAccepted : Bool :=
  accepted? (unit
    [ sdecl "Inner" [("a", uintTy), ("b", uintTy)]
    , sdecl "S"
        [ ("keep", uintTy)
        , ("label", Ty.string)
        , ("m", mapTy)
        , ("dropped", arrTy)
        , ("inner", uPath "Inner") ]
    , pubVar "s" (uPath "S") ]) == true

end GetterStructReject
end Executable
end Solidity
end SolidCore

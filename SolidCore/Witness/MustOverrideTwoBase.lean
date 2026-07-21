/-
#169 (MUST-OVERRIDE) two-base domination over-accept witnesses.

Pins a CONFIRMED over-accept fixed on the Lean side: solc 0.8.35's
`OverrideChecker::checkAmbiguousOverridesInternal` (error 6480 "Derived
contract must override function ...") runs a CUT-VERTEX analysis over the
override graph of each signature's distinct inherited declarations, and the
inherited set itself is the per-direct-base MULTISET of unshadowed
declarations (`inheritedFunctions`, including private functions). The model
used (a) a most-derived-per-key frontier and (b) a path-INSENSITIVE per-member
domination filter ("some overrider exists"), which over-accepted:

  * p17: `B` overrides BOTH unrelated roots `A` and `A2`; `C is A` re-exposes
    `A.f`. In `D is B, C` the override of `A` is not on every path (escape
    via `A2`), so `A.f` is NOT a cut vertex — solc 6480, model accepted.
  * q5: a pass-through base (`X is B, C` with `C is A` re-exposing `A.f`)
    forwards BOTH `B.f` and `A.f` (multiset, not frontier); with a deeper
    root `A3` re-exposed on another path solc 6480s `D is X, C3`.
  * q6/q7: PRIVATE functions participate (`definedFunctions()` includes
    them): two bases declaring same-signature private `f` (or private vs
    public-virtual) → 6480; the model's override members excluded private.
  * q2a/q2b: the same multiset feeds the override-LIST expectation
    (4327/2353): overriding `f` in `D is X` must name `override(A, B)`, not
    `override(B)` — the model expected exactly the frontier ({B}).

All shapes probe-confirmed against pinned solc 0.8.35 (scratchpad probes
p1-p21, q1-q7, m1-m3). Kept in the built library so `lake build SolidCore`
regression-guards them.
-/
import SolidCore.Solidity.Checked

set_option maxHeartbeats 8000000

namespace SolidCore
namespace Solidity
namespace Executable
namespace MustOverrideTwoBase

open Solidity

private def fnF (impl : Bool) (virt : Bool := true)
    (ovr : Option (List Name) := none)
    (vis : Visibility := Visibility.public_) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "f"
      visibility := some vis
      mutability := StateMutability.nonpayable
      params := []
      returns := []
      virtual := virt
      override? :=
        ovr.map (fun bs => { bases := bs.map (fun b => { segments := [b] }) })
      modifiers := []
      body := if impl then some (Stmt.block []) else none }

private def modM (impl : Bool) (virt : Bool := true)
    (ovr : Option (List Name) := none) : ContractItem :=
  ContractItem.modifierDecl
    { name := "m"
      params := []
      virtual := virt
      override? :=
        ovr.map (fun bs => { bases := bs.map (fun b => { segments := [b] }) })
      body := if impl then some (Stmt.block [Stmt.modifierPlaceholder]) else none }

private def mkC (name : Name) (abst : Bool) (bases : List Name)
    (items : List ContractItem) : SourceItem :=
  SourceItem.contract
    { kind := ContractKind.contract
      name := name
      abstract := abst
      bases := bases.map (fun b => { base := { segments := [b] } })
      items := items }

private def unit (cs : List SourceItem) : SourceUnit :=
  { items := SourceItem.pragma "solidity" "0.8.35" :: cs }

private def accepted? (u : SourceUnit) : Bool :=
  TypeCheck.sourceUnitAccepted? u

-- ===== REJECTS (solc 6480 / 4327): the fixed over-accepts. =====

/-- p17: `B` overrides unrelated roots `A`,`A2`; `C is A`; `D is B, C` →
solc 6480 (the un-overridden `A.f` escapes domination via the `A2` path). -/
def twoRootEscapeRejected : Bool :=
  accepted? (unit
    [ mkC "A" true [] [fnF false], mkC "A2" true [] [fnF false]
    , mkC "B" true ["A", "A2"] [fnF true true (some ["A", "A2"])]
    , mkC "C" true ["A"] [], mkC "D" true ["B", "C"] [] ]) == false

/-- q5: pass-through multiset — `X is B, C` forwards both `B.f` and `A.f`;
`C3` re-exposes the deeper root `A3`; `D is X, C3` → solc 6480. -/
def passThroughMultisetRejected : Bool :=
  accepted? (unit
    [ mkC "A3" true [] [fnF false]
    , mkC "A" true ["A3"] [fnF false true (some ["A3"])]
    , mkC "B" true ["A"] [fnF true true (some ["A"])]
    , mkC "C" true ["A"] [], mkC "X" true ["B", "C"] []
    , mkC "C3" true ["A3"] [], mkC "D" true ["X", "C3"] [] ]) == false

/-- q6: two bases each declaring PRIVATE `f()` → solc 6480 (private functions
are in `definedFunctions()` and participate in the ambiguity check). -/
def twoPrivateBasesRejected : Bool :=
  accepted? (unit
    [ mkC "A" false [] [fnF true false none Visibility.private_]
    , mkC "B" false [] [fnF true false none Visibility.private_]
    , mkC "C" false ["A", "B"] [] ]) == false

/-- q7: private `f` in one base + unimplemented public virtual `f` in the
other → solc 6480. -/
def privateVsVirtualRejected : Bool :=
  accepted? (unit
    [ mkC "A" false [] [fnF true false none Visibility.private_]
    , mkC "B" true [] [fnF false]
    , mkC "C" true ["A", "B"] [] ]) == false

/-- q2a: overriding through a pass-through base must name the WHOLE expected
set — `override(B)` alone → solc 4327 ("needs to specify overridden
contract A"). -/
def passThroughOverrideListRejected : Bool :=
  accepted? (unit
    [ mkC "A" true [] [fnF false]
    , mkC "B" true ["A"] [fnF true true (some ["A"])]
    , mkC "C" true ["A"] [], mkC "X" true ["B", "C"] []
    , mkC "D" false ["X"] [fnF true false (some ["B"])] ]) == false

/-- m2: the MODIFIER analogue of p17 → solc 6480 for modifiers. -/
def modifierTwoRootEscapeRejected : Bool :=
  accepted? (unit
    [ mkC "A" true [] [modM false], mkC "A2" true [] [modM false]
    , mkC "B" true ["A", "A2"] [modM true true (some ["A", "A2"])]
    , mkC "C" true ["A"] [], mkC "D" true ["B", "C"] [] ]) == false

-- ===== ACCEPTS: precision boundary — none of these may over-reject. =====

/-- p3: single-root diamond, `B` overrides the unimplemented root `A` —
`A.f` is a cut vertex and unimplemented, so `D is B, C` needs no override. -/
def singleRootDiamondAccepted : Bool :=
  accepted? (unit
    [ mkC "A" true [] [fnF false]
    , mkC "B" true ["A"] [fnF true true (some ["A"])]
    , mkC "C" true ["A"] [], mkC "D" true ["B", "C"] [] ]) == true

/-- p7: pure diamond (no redeclaration anywhere) — one declaration only. -/
def pureDiamondAccepted : Bool :=
  accepted? (unit
    [ mkC "A" true [] [fnF false], mkC "B" true ["A"] []
    , mkC "C" true ["A"] [], mkC "D" true ["B", "C"] [] ]) == true

/-- q1: pass-through base with no new exposure stays accepted. -/
def passThroughAccepted : Bool :=
  accepted? (unit
    [ mkC "A" true [] [fnF false]
    , mkC "B" true ["A"] [fnF true true (some ["A"])]
    , mkC "C" true ["A"] [], mkC "X" true ["B", "C"] []
    , mkC "D" true ["X"] [] ]) == true

/-- q2b: the FULL expected override list `override(A, B)` through a
pass-through base is accepted (the model over-rejected this before). -/
def passThroughFullOverrideListAccepted : Bool :=
  accepted? (unit
    [ mkC "A" true [] [fnF false]
    , mkC "B" true ["A"] [fnF true true (some ["A"])]
    , mkC "C" true ["A"] [], mkC "X" true ["B", "C"] []
    , mkC "D" false ["X"] [fnF true false (some ["A", "B"])] ]) == true

/-- p13-analogue: explicitly overriding in the derived contract silences the
implemented-root diamond reject. -/
def explicitOverrideAccepted : Bool :=
  accepted? (unit
    [ mkC "A" false [] [fnF true]
    , mkC "B" false ["A"] [fnF true true (some ["A"])]
    , mkC "C" false ["A"] []
    , mkC "D" false ["B", "C"] [fnF true false (some ["A", "B"])] ]) == true

/-- m3: modifier single-root diamond stays accepted. -/
def modifierSingleRootDiamondAccepted : Bool :=
  accepted? (unit
    [ mkC "A" true [] [modM false]
    , mkC "B" true ["A"] [modM true true (some ["A"])]
    , mkC "C" true ["A"] [], mkC "D" true ["B", "C"] [] ]) == true

/-- p5: implemented-root diamond (`A.f` has a body) still REJECTS — the
implemented cut vertex is not erased (pre-existing behavior kept). -/
def implementedRootDiamondRejected : Bool :=
  accepted? (unit
    [ mkC "A" false [] [fnF true]
    , mkC "B" false ["A"] [fnF true true (some ["A"])]
    , mkC "C" false ["A"] [], mkC "D" false ["B", "C"] [] ]) == false

def mustOverrideTwoBaseMatches : Bool :=
  twoRootEscapeRejected && passThroughMultisetRejected &&
    twoPrivateBasesRejected && privateVsVirtualRejected &&
    passThroughOverrideListRejected && modifierTwoRootEscapeRejected &&
    singleRootDiamondAccepted && pureDiamondAccepted &&
    passThroughAccepted && passThroughFullOverrideListAccepted &&
    explicitOverrideAccepted && modifierSingleRootDiamondAccepted &&
    implementedRootDiamondRejected

#guard mustOverrideTwoBaseMatches

end MustOverrideTwoBase
end Executable
end Solidity
end SolidCore

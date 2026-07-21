/-
#179 (USING-FIELD) struct field vs `using`-attached function name ambiguity.

Pins a CONFIRMED over-accept fixed on the Lean side: solc 0.8.35 rejects a
member access whose name is BOTH a struct field and an attached (`using L
for S`) function with error 6675 ("Member ... not unique after
argument-dependent lookup"), at the USE site — in the read form `s.a` AND
the call form `s.a()`. The collision is only an error when the attached
function actually applies to the receiver: a storage-`self` function is NOT
attached to a memory receiver (accept), while a memory-`self` function IS
attached to a storage receiver (reject). A collision that is never accessed
stays legal. The model silently resolved the field (read form) or the
attached function (call form).

All shapes probe-confirmed against pinned solc 0.8.35 (scratchpad probes
s1-s11). Kept in the built library so `lake build SolidCore`
regression-guards them.
-/
import SolidCore.Solidity.Checked

set_option maxHeartbeats 8000000

namespace SolidCore
namespace Solidity
namespace Executable
namespace UsingFieldAmbiguity

open Solidity

private def structS : SourceItem :=
  SourceItem.freeStruct
    { name := "S", fields := [{ name := "a", ty := Ty.uint 256 }] }

private def selfS : Ty := Ty.user { segments := ["S"] }

private def lib (fname : Name) (loc : DataLocation) : SourceItem :=
  SourceItem.contract
    { kind := ContractKind.library
      name := "Lib"
      abstract := false
      bases := []
      items := [ContractItem.function
        { kind := FunctionKind.function
          name := some fname
          visibility := some Visibility.internal_
          mutability :=
            if loc == DataLocation.storage then StateMutability.view
            else StateMutability.pure
          params := [{ name := some "s", ty := selfS, location := some loc }]
          returns := [{ name := none, ty := Ty.uint 256 }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [Stmt.returnValues (some (Expr.literal (Literal.number "7")))]) }] }

private def usingItem : ContractItem :=
  ContractItem.usingDecl
    { library := { segments := ["Lib"] }, target := some selfS }

private def gWith (body : List Stmt)
    (sm : StateMutability := StateMutability.pure) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "g"
      visibility := some Visibility.public_
      mutability := sm
      params := []
      returns := [{ name := none, ty := Ty.uint 256 }]
      virtual := false
      override? := none
      modifiers := []
      body := some (Stmt.block body) }

/-- `S memory s = S(5); return s.<m>` (or `s.<m>()`). -/
private def useMem (m : Name) (callForm : Bool) : SourceItem :=
  SourceItem.contract
    { kind := ContractKind.contract
      name := "T"
      abstract := false
      bases := []
      items := [usingItem, gWith
        [ Stmt.varDecl
            [{ name := some "s", ty := some selfS
               location := some DataLocation.memory }]
            (some (Expr.call (Expr.typeName selfS)
              [Arg.positional (Expr.literal (Literal.number "5"))]))
        , Stmt.returnValues (some
            (if callForm then
              Expr.call (Expr.member (Expr.ident "s") m) []
            else
              Expr.member (Expr.ident "s") m)) ]] }

/-- `S internal st; ... return st.<m>` (storage receiver, read form). -/
private def useSto (m : Name) : SourceItem :=
  SourceItem.contract
    { kind := ContractKind.contract
      name := "T"
      abstract := false
      bases := []
      items :=
        [ usingItem
        , ContractItem.stateVar
            { name := "st", ty := selfS
              visibility := some Visibility.internal_
              mutability := VarMutability.mutable
              override? := none
              init := none }
        , gWith [Stmt.returnValues (some (Expr.member (Expr.ident "st") m))]
            StateMutability.view ]}

private def unit (cs : List SourceItem) : SourceUnit :=
  { items := SourceItem.pragma "solidity" "0.8.35" :: cs }

private def accepted? (u : SourceUnit) : Bool :=
  TypeCheck.sourceUnitAccepted? u

-- ===== REJECTS (solc 6675): the fixed over-accepts. =====

/-- s1: memory receiver, READ form `s.a`, memory-self `Lib.a` attached. -/
def fieldReadCollisionRejected : Bool :=
  accepted? (unit [structS, lib "a" DataLocation.memory, useMem "a" false])
    == false

/-- s4: CALL form `s.a()` with the same collision. -/
def fieldCallCollisionRejected : Bool :=
  accepted? (unit [structS, lib "a" DataLocation.memory, useMem "a" true])
    == false

/-- s6: storage receiver, storage-self `Lib.a` attached, read `st.a`. -/
def storageFieldReadCollisionRejected : Bool :=
  accepted? (unit [structS, lib "a" DataLocation.storage, useSto "a"])
    == false

/-- s9: a MEMORY-self function IS attached to a storage receiver → still
ambiguous. -/
def memorySelfOnStorageReceiverRejected : Bool :=
  accepted? (unit [structS, lib "a" DataLocation.memory, useSto "a"])
    == false

-- ===== ACCEPTS: precision boundary — none of these may over-reject. =====

/-- s2: the collision exists but the member is never ACCESSED. -/
def unusedCollisionAccepted : Bool :=
  accepted? (unit
    [ structS, lib "a" DataLocation.memory
    , SourceItem.contract
        { kind := ContractKind.contract
          name := "T"
          abstract := false
          bases := []
          items := [usingItem, gWith
            [Stmt.returnValues (some (Expr.literal (Literal.number "2")))]] } ])
    == true

/-- s3: no collision — attached `b` called on a struct with field `a`. -/
def distinctNamesAccepted : Bool :=
  accepted? (unit [structS, lib "b" DataLocation.memory, useMem "b" true])
    == true

/-- s8: a STORAGE-self function is NOT attached to a memory receiver, so the
field read stays unambiguous. -/
def storageSelfOnMemoryReceiverAccepted : Bool :=
  accepted? (unit [structS, lib "a" DataLocation.storage, useMem "a" false])
    == true

def usingFieldAmbiguityMatches : Bool :=
  fieldReadCollisionRejected && fieldCallCollisionRejected &&
    storageFieldReadCollisionRejected && memorySelfOnStorageReceiverRejected &&
    unusedCollisionAccepted && distinctNamesAccepted &&
    storageSelfOnMemoryReceiverAccepted

#guard usingFieldAmbiguityMatches

end UsingFieldAmbiguity
end Executable
end Solidity
end SolidCore

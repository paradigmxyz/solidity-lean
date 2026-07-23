/-
Storage inline-array-literal element-widening boundary witnesses (2026-07-23).

Companion to `ArrayLiteralWiden` (which pins the MEMORY rule). solc 0.8.35 types
an inline array literal bottom-up (smallest common mobile element type, e.g.
`[1,2,3] : uint8[3]`). A fixed→fixed MEMORY conversion needs an IDENTICAL element
type (the classic `uint8[3] ↛ uint256[3]` gotcha, kept green by
`ArrayLiteralWiden`). But initializing a NON-POINTER STORAGE array — a state
variable — runs solc's storage-copy conversion branch
(`ArrayType::isImplicitlyConvertibleTo`, `Types.cpp:1640-1648`), where each
element only needs to be IMPLICITLY CONVERTIBLE. So a state variable
`uint256[2] arr = [50,0];` is ACCEPTED even though the memory twin is rejected.

This typechecker previously applied the memory identity rule to state-variable
initializers too and OVER-REJECTED every widening state var
(`expectedType(u256[2])(u256[2])`, the printed types coinciding because the
literal's `checkExpr` type is the target-wide `uint256[2]`). It now mirrors solc:
storage widening ACCEPTS, storage sign-change / narrowing still REJECTS, and the
memory twin still REJECTS.

Each `…Accepted : Bool := sourceUnitAccepted? …` pins a program pinned-solc
0.8.35 ACCEPTS; each `…Rejected : Bool := Result.isError (SourceUnit.check …)`
pins one it REJECTS. Verified against the pinned binary (2026-07-23). Helpers
come from `SolidCore.Witness.TypeCheck`.
-/
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

-- Local shorthands.
private def salwNum (s : String) : Expr := numberExpr s
private def salwArr (elemTy : Ty) (k : Nat) : Ty := Ty.array elemTy (some k)
private def salwConv (ty : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional e]
private def salwNeg (e : Expr) : Expr := Expr.unary UnaryOp.neg e

-- A contract with a single public STATE VARIABLE `T arr = <init>;`.
private def salwStateVarSU (ty : Ty) (init : Expr) : SourceUnit :=
  { items := [SourceItem.contract
      { name := "C"
        items :=
          [ ContractItem.stateVar
              { name := "arr", ty := ty,
                visibility := some Visibility.public_, init := some init } ] }] }

-- A single pure function declaring `T memory x = <init>;` (the memory twin).
private def salwMemDeclSU (ty : Ty) (init : Expr) : SourceUnit :=
  { items := [SourceItem.contract
      { name := "C"
        items := [ContractItem.function
          { simpleReturnFunction with
              name := some "f"
              mutability := StateMutability.pure
              returns := []
              body := some (Stmt.block
                [ Stmt.varDecl
                    [ { name := some "x", ty := some ty,
                        location := some DataLocation.memory } ]
                    (some init) ]) }] }] }

private def salw50 : Expr := Expr.array [salwNum "50", salwNum "0"]
private def salw123 : Expr := Expr.array [salwNum "1", salwNum "2", salwNum "3"]

-- ===========================================================================
-- ACCEPTED — storage state-variable initializer widens the literal
-- ===========================================================================

-- `uint256[2] arr = [50,0];`  (the submitted divergence; uint8[2] → uint256[2])
def salwStateWiden256Accepted : Bool :=
  sourceUnitAccepted? (salwStateVarSU (salwArr (Ty.uint 256) 2) salw50)

-- `uint16[3] arr = [1,2,3];`  (uint8[3] → uint16[3])
def salwStateWiden16Accepted : Bool :=
  sourceUnitAccepted? (salwStateVarSU (salwArr (Ty.uint 16) 3) salw123)

-- `uint256[2][2] arr = [[1,2],[3,4]];`  (nested uint8[2][2] → uint256[2][2])
def salwStateWidenMultidimAccepted : Bool :=
  sourceUnitAccepted? (salwStateVarSU (salwArr (salwArr (Ty.uint 256) 2) 2)
    (Expr.array
      [ Expr.array [salwNum "1", salwNum "2"]
      , Expr.array [salwNum "3", salwNum "4"] ]))

-- `uint256[2] arr = [uint8(1),2];`  (typed lead still widens for storage)
def salwStateTypedLeadWidenAccepted : Bool :=
  sourceUnitAccepted? (salwStateVarSU (salwArr (Ty.uint 256) 2)
    (Expr.array [salwConv (Ty.uint 8) (salwNum "1"), salwNum "2"]))

-- `int16[2] arr = [int8(-1),2];`  (signed widen int8[2] → int16[2])
def salwStateSignedWidenAccepted : Bool :=
  sourceUnitAccepted? (salwStateVarSU (salwArr (Ty.int 16) 2)
    (Expr.array [salwConv (Ty.int 8) (salwNeg (salwNum "1")), salwNum "2"]))

-- `uint8[2] arr = [1,2];`  (identity — must remain accepted)
def salwStateIdentityAccepted : Bool :=
  sourceUnitAccepted? (salwStateVarSU (salwArr (Ty.uint 8) 2)
    (Expr.array [salwNum "1", salwNum "2"]))

-- `uint256[2] arr = [uint256(50),0];`  (explicit element — already accepted)
def salwStateExplicitAccepted : Bool :=
  sourceUnitAccepted? (salwStateVarSU (salwArr (Ty.uint 256) 2)
    (Expr.array [salwConv (Ty.uint 256) (salwNum "50"), salwNum "0"]))

def salwAllAccepted : Bool :=
  salwStateWiden256Accepted && salwStateWiden16Accepted &&
    salwStateWidenMultidimAccepted && salwStateTypedLeadWidenAccepted &&
    salwStateSignedWidenAccepted && salwStateIdentityAccepted &&
    salwStateExplicitAccepted

-- ===========================================================================
-- REJECTED — storage cases solc still rejects (sign change / narrowing / over-
-- flow / wrong length), and the MEMORY twin (the gotcha must stay intact)
-- ===========================================================================

-- `uint256[2] arr = [-1,2];`  (int8[2] ↛ uint256[2]; sign change)
def salwStateSignChangeRejected : Bool :=
  Result.isError (SourceUnit.check
    (salwStateVarSU (salwArr (Ty.uint 256) 2)
      (Expr.array [salwNeg (salwNum "1"), salwNum "2"])))

-- `uint8[2] arr = [1,256];`  (uint16[2] ↛ uint8[2]; element overflow)
def salwStateOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    (salwStateVarSU (salwArr (Ty.uint 8) 2)
      (Expr.array [salwNum "1", salwNum "256"])))

-- `uint8[2] arr = [uint16(1),2];`  (uint16[2] ↛ uint8[2]; typed narrowing)
def salwStateNarrowTypedRejected : Bool :=
  Result.isError (SourceUnit.check
    (salwStateVarSU (salwArr (Ty.uint 8) 2)
      (Expr.array [salwConv (Ty.uint 16) (salwNum "1"), salwNum "2"])))

-- `uint256[2] arr = [1,2,3];`  (wrong length)
def salwStateWrongLengthRejected : Bool :=
  Result.isError (SourceUnit.check
    (salwStateVarSU (salwArr (Ty.uint 256) 2) salw123))

-- MEMORY twin `uint256[2] memory x = [50,0];`  (the gotcha — STILL rejected)
def salwMemWiden256StillRejected : Bool :=
  Result.isError (SourceUnit.check
    (salwMemDeclSU (salwArr (Ty.uint 256) 2) salw50))

-- MEMORY twin `uint16[3] memory x = [1,2,3];`  (STILL rejected)
def salwMemWiden16StillRejected : Bool :=
  Result.isError (SourceUnit.check
    (salwMemDeclSU (salwArr (Ty.uint 16) 3) salw123))

def salwAllRejected : Bool :=
  salwStateSignChangeRejected && salwStateOverflowRejected &&
    salwStateNarrowTypedRejected && salwStateWrongLengthRejected &&
    salwMemWiden256StillRejected && salwMemWiden16StillRejected

end Examples
end TypeCheck
end Solidity
end SolidCore



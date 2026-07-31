import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NESTED-ARRAY-LITERAL-STORAGE-COPY (task #72, over_reject + fail-closed).

  contract C {
    uint8[][2][] a3 = new uint8[][2][](1);
    constructor() { a3[0][1] = [5, 6]; }
    function test1() public returns (uint8[][] memory) {}
  }

solc 0.8.35 + EVM ACCEPT and deploy this: an inline array literal `[5,6]` is
typed BOTTOM-UP as `uint8[2] memory` and COPIED into the dynamic storage array
element `a3[0][1] : uint8[]` (fixed→dynamic storage-copy: resize to the source
length, copy each element). The resulting storage is
  slot 0                = 1     (a3.length)
  keccak(0)             = 0     (a3[0][0].length)
  keccak(0)+1           = 2     (a3[0][1].length)
  keccak(keccak(0)+1)   = 0x0605 = 1541  (elements 5,6 packed, little-endian)

solidity-lean previously FAILED CLOSED at typecheck (over_reject: `[5,6]` got the
over-wide `uint256[2]` `checked.ty`, and the storage-copy assignment branch used
that instead of solc's bottom-up mobile type `uint8[2]`). Accepting it then
Panic(0)'d at RUN: storing the memory-literal `Value.fixedArray` into a
`StorageLayout.dynamicArray` demanded a `Value.dynamicArray`.

Two-part fix:
  * TypeCheck: the storage-array copy branch of `=` substitutes the inline
    literal's bottom-up type for its over-wide `checked.ty`.
  * Interpreter: `State.storeStorageLayoutAt` accepts a `Value.fixedArray` at a
    `dynamicArray` layout (resize to the source length, copy) — the fixed→dynamic
    storage copy.

The pinned slots below are solc+EVM's measured storage (arena adjudicator).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace NestedArrayLiteralStorageCopy

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (s : String) : Expr := Expr.literal (Literal.number s)

-- uint8[][2][]
private def a3Ty : Ty :=
  Ty.array (Ty.array (Ty.array (Ty.uint 8) none) (some 2)) none

private def ctor : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.constructor
      visibility := some Visibility.public_
      body := some (Stmt.block
        [ Stmt.expr (Expr.assign
            (Expr.index (Expr.index (Expr.ident "a3") (num "0")) (num "1"))
            AssignOp.assign
            (Expr.array [num "5", num "6"])) ]) }

private def test1 : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "test1"
      visibility := some Visibility.public_
      returns := [{ name := none, ty := Ty.array (Ty.array (Ty.uint 8) none) none,
                    location := some DataLocation.memory }]
      body := some (Stmt.block []) }

def contract : ContractDecl :=
  { name := "C"
    items :=
      [ ContractItem.stateVar
          { name := "a3", ty := a3Ty
            init := some (Expr.newExpr a3Ty [Arg.positional (num "1")]) }
      , ctor
      , test1 ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

-- Typechecks (was fail-closed over_reject).
def accepted : Bool :=
  TypeCheck.Result.isOk (TypecheckedInput.checkedSourceUnit sourceUnit)

-- Deploy (run constructor), then read a storage slot; `none` on revert/non-return.
private def deploySlot? (su : SourceUnit) (slot : Word) : Option Word :=
  match CheckedInput.constructContract 500 su "C" State.empty [] with
  | Except.ok (SolidCore.Solidity.Source.CallResult.returned st _) =>
      some (st.loadSlot slot)
  | _ => none

-- The four measured solc+EVM storage slots (arena adjudicator).
def a3LengthSlot : Option Word := deploySlot? sourceUnit 0
def a3_0_0_lengthSlot : Option Word :=
  deploySlot? sourceUnit
    18569430475105882587588266137607568536673111973893317399460219858819262702947
def a3_0_1_lengthSlot : Option Word :=
  deploySlot? sourceUnit
    18569430475105882587588266137607568536673111973893317399460219858819262702948
def a3_0_1_dataSlot : Option Word :=
  deploySlot? sourceUnit
    48884853742542595708534018066926377678352722966659282746029169750040480094106

-- ---------------------------------------------------------------------------
-- Flat control: `uint8[] a; constructor { a = [5,6]; }`  (the fixed→dynamic
-- storage copy, un-nested).  slot 0 = length 2, keccak(0) = 0x0605.
-- ---------------------------------------------------------------------------
private def flatSU : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract
      { name := "C"
        items :=
          [ ContractItem.stateVar { name := "a", ty := Ty.array (Ty.uint 8) none }
          , ContractItem.function
              { kind := FunctionKind.constructor
                visibility := some Visibility.public_
                body := some (Stmt.block
                  [ Stmt.expr (Expr.assign (Expr.ident "a") AssignOp.assign
                      (Expr.array [num "5", num "6"])) ]) } ] }] }

def flatAccepted : Bool :=
  TypeCheck.Result.isOk (TypecheckedInput.checkedSourceUnit flatSU)
def flatLengthSlot : Option Word := deploySlot? flatSU 0
def flatDataSlot : Option Word :=
  deploySlot? flatSU
    18569430475105882587588266137607568536673111973893317399460219858819262702947

-- ---------------------------------------------------------------------------
-- Fixed control (unchanged): `uint8[2] a; constructor { a = [5,6]; }`.
-- ---------------------------------------------------------------------------
private def fixedSU : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract
      { name := "C"
        items :=
          [ ContractItem.stateVar { name := "a", ty := Ty.array (Ty.uint 8) (some 2) }
          , ContractItem.function
              { kind := FunctionKind.constructor
                visibility := some Visibility.public_
                body := some (Stmt.block
                  [ Stmt.expr (Expr.assign (Expr.ident "a") AssignOp.assign
                      (Expr.array [num "5", num "6"])) ]) } ] }] }

def fixedDataSlot : Option Word := deploySlot? fixedSU 0

#guard accepted
#guard a3LengthSlot == some 1
#guard a3_0_0_lengthSlot == some 0
#guard a3_0_1_lengthSlot == some 2
#guard a3_0_1_dataSlot == some 1541
#guard flatAccepted
#guard flatLengthSlot == some 2
#guard flatDataSlot == some 1541
#guard fixedDataSlot == some 1541

end NestedArrayLiteralStorageCopy
end Witness
end Solidity
end SolidCore

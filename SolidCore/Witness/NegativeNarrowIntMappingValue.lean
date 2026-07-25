import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
NEGATIVE-NARROW-INT-MAPPING-VALUE (regression): a narrow SIGNED int mapping
value stored a negative value —

  mapping(uint256 => int8) mv;
  function run() public returns (uint256) {
    mv[3] = int8(-1);
    return uint256(int256(mv[3]));
  }

Real solc 0.8.35 + EVM: the `int8` mapping value occupies only the LOW byte of
its value slot, so `mv[3] = int8(-1)` masks the sign-extended word to 1 byte and
writes 0xff (255); the high 31 bytes stay zero. `run()` returns 2^256-1.

The bug: a mapping value derives its layout purely from
`Ty.toCoreStorageLayout? valueTy`, whose narrow-int fallback erases the width to
`scalar int256`. Unlike a standalone/packed narrow int (which carries `bits/8` on
the `StorageField` record / a packed member layout and masks on store), the
mapping value had neither, so `int8(-1)` stored the FULL sign-extended word
0xff..ff (2^256-1) into the value slot — corrupting anything else that would be
packed there. The return value agreed (the read sign-extends either way), so only
the post-call storage word exposed the divergence.

Fix: `Ty.toCoreStorageLayout?` `Ty.mapping` case now carries a narrow SIGNED int
value as a `packedScalar 0 (bits/8) true int256` lane, so the store masks to the
type width (0xff) exactly as solc does.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace NegativeNarrowIntMappingValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def neg (e : Expr) : Expr := Expr.unary UnaryOp.neg e
private def cast (ty : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional e]

-- The value slot for mapping key 3 under a mapping at slot 0.
-- keccak256(abi.encode(uint256(3), uint256(0))).
private def mvSlot3 : Word :=
  7290387335634266486249037663595860854047133815481999773725367799777733655939

-- mv[3] = int8(-1);
private def storeStmt : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.index (Expr.ident "mv") (lit "3"))
    AssignOp.assign
    (cast (Ty.int 8) (neg (lit "1"))))

-- return uint256(int256(mv[3]));
private def retStmt : Stmt :=
  Stmt.returnValues (some
    (cast (Ty.uint 256)
      (cast (Ty.int 256) (Expr.index (Expr.ident "mv") (lit "3")))))

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "mv"
          ty := Ty.mapping (Ty.uint 256) (Ty.int 8)
          visibility := some Visibility.internal_
          mutability := VarMutability.mutable
          override? := none
          init := none }
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.public_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block [ storeStmt, retStmt ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- Real solc 0.8.35 + EVM ground truth: `run()` returns 2^256-1.
def run_returns_max : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty []
    (2 ^ 256 - 1)

-- The observable divergence: the mapping value slot for key 3 holds 0xff (255),
-- NOT the sign-extended 2^256-1.
def value_slot_is_masked_byte : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run" State.empty []
  Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot mvSlot3) 255)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_max
#guard isOkTrue value_slot_is_masked_byte

end NegativeNarrowIntMappingValue
end Witness
end Solidity
end SolidCore

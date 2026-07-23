import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
BYTES-OF-STRING-LVALUE (divergence): indexing a `bytes(...)`/`string(...)`
REINTERPRET of a dynamic `string`/`bytes` lvalue is itself an lvalue, so it can
be written through —

  string s;
  function run() external returns (string memory, uint256, bytes1) {
    s = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!"; // 63 bytes
    string memory m = s;      // deep copy storage -> memory
    bytes(m)[62] = 0x3F;      // mutate memory copy's last byte '!'(0x21) -> '?'(0x3f)
    return (m, bytes(s).length, bytes(s)[62]);
  }

Real solc 0.8.35 + EVM ground truth: `bytes(m)` is a pointer REINTERPRET of the
`string memory m` (identical layout), yielding a reference that aliases m's
memory. `bytes(m)[62]` is therefore an assignable lvalue; writing 0x3F mutates
only the memory copy `m`, leaving the storage string `s` untouched. So `run()`
returns (m = the 63-byte string with last byte 0x3F, bytes(s).length = 63,
bytes(s)[62] = 0x21).

The bug: the typechecker's type-conversion arm hard-coded `lvalue := false` for
EVERY conversion, so `bytes(m)` was a non-lvalue and `bytes(m)[62]` failed the
assignment-target lvalue check (TypeError.expectedLValue) — solidity-lean
fail-closed / over-reject on a solc-accepted program. Fix: a string<->bytes
reinterpret conversion propagates the operand's lvalue/state-lvalue/data-location,
and `Expr.toCoreLValue?` peels the transparent conversion when lowering the
write target.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace BytesOfStringLValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def theString : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!"

-- bytes(<ident>) as an expression
private def bytesOf (name : String) : Expr :=
  Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.ident name)]

-- s = "abc...!"
private def assignS : Stmt :=
  Stmt.expr (Expr.assign (Expr.ident "s") AssignOp.assign
    (Expr.literal (Literal.string theString)))

-- string memory m = s;
private def declM : Stmt :=
  Stmt.varDecl
    [{ name := some "m", ty := Ty.string, location := some DataLocation.memory }]
    (some (Expr.ident "s"))

-- bytes(m)[62] = 0x3F;
private def mutateM : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.index (bytesOf "m") (Expr.literal (Literal.number "62")))
    AssignOp.assign
    (Expr.literal (Literal.number "0x3f")))

-- return (m, bytes(s).length, bytes(s)[62]);
private def retStmt : Stmt :=
  Stmt.returnValues (some (Expr.tuple
    [ TupleItem.value (Expr.ident "m")
    , TupleItem.value (Expr.member (bytesOf "s") "length")
    , TupleItem.value (Expr.index (bytesOf "s") (Expr.literal (Literal.number "62"))) ]))

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "s", ty := Ty.string, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          params := []
          returns :=
            [{ name := none, ty := Ty.string, location := some DataLocation.memory }
            , { name := none, ty := Ty.uint 256, location := none }
            , { name := none, ty := Ty.bytesN 1, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block [assignS, declM, mutateM, retStmt]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

#guard accepted

-- Expected ABI return data (verified against the adjudicator's real-EVM
-- measurement). Tuple `(string memory, uint256, bytes1)`:
--   word(0x60)  head offset to the string tail
--   word(63)    uint256 bytes(s).length
--   0x21 <<     bytes1 bytes(s)[62]  (left-aligned)
--   word(63)    string length
--   data...     the 63 string bytes (byte 62 = 0x3F), right-padded to 64
private def word (n : Nat) : List Byte := List.replicate 31 0 ++ [n]

private def bytes1Word (b : Byte) : List Byte := b :: List.replicate 31 0

private def padR32 (bs : List Byte) : List Byte :=
  bs ++ List.replicate ((32 - bs.length % 32) % 32) 0

-- m's bytes: the string with its final byte replaced by 0x3F ('?').
private def mBytes : List Byte :=
  (Executable.stringUtf8Bytes theString).dropLast ++ [0x3f]

def expectedOutput : List Byte :=
  word 0x60 ++ word 63 ++ bytes1Word 0x21 ++ word 63 ++ padR32 mBytes

def runMatches : Except TypeError Bool :=
  Examples.checkedContractAbiOutputMatches 4096 runContract "run" [] (some expectedOutput)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

-- Storage `s` must be UNTOUCHED by the memory mutation: bytes(s)[62] stays 0x21.
def storageUnchanged : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run"
    SolidCore.Solidity.Source.State.empty []
  -- slot 0 low byte holds 2*length+1 for a short/long string; length 63 => long
  -- string (slot holds 2*63+1 = 127), contents live at keccak(0)+.  We assert the
  -- observable already checked by `runMatches` (bytes(s)[62]=0x21) rather than
  -- re-deriving the long-string layout here.
  Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 127)

#guard isOkTrue runMatches
#guard isOkTrue storageUnchanged

end BytesOfStringLValue
end Witness
end Solidity
end SolidCore

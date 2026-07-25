import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NARROW-SHL-WIDE-CAST-RETURN (S, narrow-shl-mask-widening-cast-return) — a
WORD-width (`uint256`) explicit cast of a NARROW left-shift sub-expression must
still evaluate that shift at ITS OWN operand width, so the high bits shifted past
the narrow type are TRUNCATED (masked) BEFORE the widening conversion.

`f(uint8 a, uint8 b) returns (uint256) { return uint256(a << b); }` with
`f(1, 8)`: solc types `a << b` at the LEFT-operand width (`uint8`) and cleans
the result with `cleanup_t_uint8` (a TRUNCATING cast — shifts never
overflow-panic), so `1 << 8` drops the bits above bit 7 and yields `0`; the
`uint256(...)` widening then produces `0`. solidity-lean formerly routed the
WIDE (`uint256`) cast through the env-less Direct path (the
`Ty.wordIntCastTarget?` arm of `Expr.toCoreAsWithEnvFuel?` only rerouted the
signed-literal-mix and narrow-checked-ARITHMETIC cases), so `a << b` ran at 256
bits (= `1 << 8 = 256`, unmasked) and the call returned 256 — a wrong-value
soundness gap.

The narrow-add-wide-cast arm already re-runs narrow checked arithmetic at the
operand width; the fix broadens the WIDE-cast arm's reroute gate so
`uint256(a << b)` over a NARROW shift likewise lowers the argument at its OWN
type (`uint8`) through the env-aware recursion (whose Direct fallback fires the
truncating `uint8` cleanup on the shift) before the 256-bit widening. A safe
(in-range) shift and an explicitly-widened shift keep the byte-identical 256-bit
path.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace NarrowShlWideCastReturnWitness

open SolidCore.Solidity.Source

private def a : Expr := Expr.ident "a"
private def b : Expr := Expr.ident "b"
private def shl (x y : Expr) : Expr := Expr.binary BinaryOp.shl x y
private def u256 (e : Expr) : Expr := Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]

private def u8u8ReturnsU256 (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none },
               { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }

-- The submission: `return uint256(a << b);`.
private def fFn : ContractItem := u8u8ReturnsU256 "f" (u256 (shl a b))
-- CONTROL: explicitly-widened operand `uint256(uint256(a) << b)` shifts at 256
-- bits — no mask — so `1 << 8 = 256` is preserved.
private def gFn : ContractItem :=
  u8u8ReturnsU256 "g" (u256 (shl (u256 a) b))

-- EXACT SUBMISSION shape (uint32 local initialized to `type(uint32).max`, then a
-- word cast of the narrow shift):
--   run() returns (uint256) { uint32 x = type(uint32).max; return uint256(x << 8); }
-- solc+EVM: `0xFFFFFFFF << 8` truncated to uint32 = `0xFFFFFF00` = 4294967040.
-- The env-less path returned the un-masked `0xFFFFFFFF00` = 1099511627520.
private def runFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "run",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "x", ty := some (Ty.uint 32), location := none }]
          (some (Expr.member (Expr.typeName (Ty.uint 32)) "max"))
      , Stmt.returnValues
          (some (u256 (shl (Expr.ident "x") (Expr.literal (Literal.number "8"))))) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [fFn, gFn, runFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end NarrowShlWideCastReturnWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace NarrowShlWideCastReturn

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.NarrowShlWideCastReturnWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.NarrowShlWideCastReturnWitness.importedContractAccepted

-- The submission call f(1, 8): `1 << 8` at uint8 truncates to 0 (matches
-- solc+EVM), NOT the un-masked 256 the env-less path returned.
def f_1_8_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 1, Value.word 8] 0

-- f(1, 7): `1 << 7 = 128` fits in uint8 -> returns 128 (safe control).
def f_1_7_is_128 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 1, Value.word 7] 128

-- f(3, 6): `3 << 6 = 192` fits in uint8 -> 192.
def f_3_6_is_192 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 3, Value.word 6] 192

-- f(3, 7): `3 << 7 = 384`, masked to uint8 = 128 (0x80).
def f_3_7_is_128 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 3, Value.word 7] 128

-- CONTROL (minimality): g(1,8) with explicitly-widened operand
-- `uint256(uint256(a) << b)` shifts at 256 bits -> 256, no mask.
def g_1_8_is_256 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "g" State.empty
    [Value.word 1, Value.word 8] 256

-- EXACT SUBMISSION: run() = uint256((uint32 max) << 8) = 0xFFFFFF00 = 4294967040
-- (masked to uint32), NOT the un-masked 0xFFFFFFFF00 = 1099511627520.
def run_is_4294967040 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "run" State.empty [] 4294967040

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue f_1_8_is_0
#guard isOkTrue f_1_7_is_128
#guard isOkTrue f_3_6_is_192
#guard isOkTrue f_3_7_is_128
#guard isOkTrue g_1_8_is_256
#guard isOkTrue run_is_4294967040

end NarrowShlWideCastReturn
end Witness
end Solidity
end SolidCore

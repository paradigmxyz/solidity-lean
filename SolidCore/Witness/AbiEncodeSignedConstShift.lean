import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-SIGNED-CONST-SHIFT (S, signed-constant-shift-in-abiencode-arg) — a
CONSTANT-FOLDED SIGNED shift used directly as an `abi.encode`/`abi.encodePacked`
argument.

`return abi.encode(int256(5) >> 1);`: solc constant-folds `int256(5) >> 1` to the
`int256` value `2` and encodes its 32-byte word (`0x…02`). solidity-lean lowered
the argument through the env-less arg path (`Expr.toAbiEncodeArg?` →
`Expr.toCore?`); the binary-fold arm of `Expr.toCore?` folds any numeric binary to
a plain `Expr.word` (it is target-less and discards the operand signedness the
surrounding `int256(...)` cast established), so the folded constant reaches the
signed `int256` abi slot at RUNTIME as a `Value.word`, not a `Value.int`. The
static scalar encoders (`abiStaticBytes?` / `abiEncodePackedValue?`) accepted only
`Ty.int256, Value.int`, so the `Value.word` fell through to `none` →
`RevertData.typeMismatch` = a SPURIOUS `Panic(0)` (revert-vs-success), where
solc+EVM succeed with `0x…02`.

This is NOT the narrow-cleanup/missing-mask family: it reproduces at FULL width
`int256`, needs no narrow type and no runtime argument, and it is an OVER-revert
(the model invents a panic), not a wrong value. It fires only for a signed
constant-folded operator that the fold routes to a bare `Expr.word` and that does
NOT reroute to the env-aware typed path — i.e. `>>` in `abi.encode*` arg position
(`+`/`-`/… reroute via `peelToOverflowArithmetic?`; a variable operand is not
folded; `<<` reroutes via `peelToNarrowShl?` and lowers env-aware to a
`Value.int`; a shift OUTSIDE a builtin arg is not encoded as `int256`).

The fix adds a `Ty.int256, Value.word` arm to both static scalar abi encoders
(`abiStaticBytes?` and `abiEncodePackedValue?`): a `Value.word` reaching an
`int256` slot is a folded constant that fits `int256` (typecheck bounds it to
< 2^255, high bit clear), so its word bits ARE the correct 2's-complement and the
boundary bytes are byte-identical to the `Value.int` encoding — no Panic(0).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeSignedConstShift

open SolidCore.Solidity.Source

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def abiEncodePacked (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args
private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def i256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.int 256)) [Arg.positional e]
private def u256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]
private def shr (x y : Expr) : Expr := Expr.binary BinaryOp.shr x y
private def shl (x y : Expr) : Expr := Expr.binary BinaryOp.shl x y
private def add (x y : Expr) : Expr := Expr.binary BinaryOp.add x y

private def bytesFn (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }

-- The submission: `abi.encode(int256(5) >> 1)` = the 32-byte word 2.
private def fFn : ContractItem :=
  bytesFn "f" (abiEncode [Arg.positional (shr (i256 (num "5")) (num "1"))])
-- FAMILY: same trigger under `abi.encodePacked` (packed int256 is a full 32-byte
-- word) = 2.
private def fpFn : ContractItem :=
  bytesFn "fp" (abiEncodePacked [Arg.positional (shr (i256 (num "5")) (num "1"))])
-- CONTROL (unsigned shift, already agreed): `abi.encode(uint256(5) >> 1)` = 2.
private def gFn : ContractItem :=
  bytesFn "g" (abiEncode [Arg.positional (shr (u256 (num "5")) (num "1"))])
-- CONTROL (signed constant arithmetic, reroutes env-aware, already agreed):
-- `abi.encode(int256(5) + int256(1))` = 6.
private def hFn : ContractItem :=
  bytesFn "h" (abiEncode [Arg.positional (add (i256 (num "5")) (i256 (num "1")))])
-- CONTROL (signed LEFT shift, reroutes env-aware, already agreed):
-- `abi.encode(int256(5) << 1)` = 10.
private def mFn : ContractItem :=
  bytesFn "m" (abiEncode [Arg.positional (shl (i256 (num "5")) (num "1"))])
-- CONTROL (no shift, already agreed): `abi.encode(int256(5))` = 5.
private def kFn : ContractItem :=
  bytesFn "k" (abiEncode [Arg.positional (i256 (num "5"))])

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [fFn, fpFn, gFn, hFn, mFn, kFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeSignedConstShift
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeSignedConstShift

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeSignedConstShift.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeSignedConstShift.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n

-- The submission `f()`: `abi.encode(int256(5) >> 1)` = the 32-byte word 2 (solc+EVM),
-- NOT the spurious Panic(0) the env-less signed-fold path produced.
def f_encodes_2 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty [] (w32 2)
def fp_encodes_2 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "fp" State.empty [] (w32 2)
def g_encodes_2 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "g" State.empty [] (w32 2)
def h_encodes_6 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "h" State.empty [] (w32 6)
def m_encodes_10 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "m" State.empty [] (w32 10)
def k_encodes_5 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "k" State.empty [] (w32 5)

#guard accepted
#guard isOkTrue f_encodes_2
#guard isOkTrue fp_encodes_2
#guard isOkTrue g_encodes_2
#guard isOkTrue h_encodes_6
#guard isOkTrue m_encodes_10
#guard isOkTrue k_encodes_5

end AbiEncodeSignedConstShift
end Witness
end Solidity
end SolidCore

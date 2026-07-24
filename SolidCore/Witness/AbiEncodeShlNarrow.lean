import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-SHL-NARROW (S, narrow-shl-mask-in-abiencode-arg) — a narrow
(`uintN`/`intN`, N < 256) left shift `a << b` used directly as an `abi.encode`
argument.

`return abi.encode(a << b)` with `uint8 a = 1, b = 8`: solc types the shift at
the LEFT-operand width (`uint8`) and cleans the result with `cleanup_t_uint8`
(a TRUNCATING cast — shifts never overflow-panic, even in a checked block), so
`1 << 8` drops the bits above bit 7 and encodes `0`. solidity-lean lowered the
`abi.encode` argument through the env-LESS path (`Expr.toAbiEncodeArg?` →
`Expr.toCore?`). `annotateAbi` wraps the argument in the redundant narrow cast
`uint8(a << b)` (the operand type it recovers WITH the env), but the env-less
cast lowering DROPS that cast when it cannot env-lessly type the shift operands
(parameter/local idents have no `Expr.abiTy?` arm), leaving a bare 256-bit
`shl`. So `1 << 8 = 256` was encoded (`0x…0100`) — a wrong-value soundness gap.

The fix adds `Expr.peelToNarrowShl?` to the reroute predicate
`Expr.abiArgNeedsEnvCleanupFuel?` (it peels the redundant narrow cast to reach
the `<<`), so the argument routes through the env-aware recursion, whose Direct
fallback (`Expr.toCoreAs?`) fires `implicitCleanupCore?`'s truncating
`uintCast`/`intCast` for a left shift at the operand width. A safe (in-range)
shift stays byte-identical (control below).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeShlNarrow

open SolidCore.Solidity.Source

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def a : Expr := Expr.ident "a"
private def b : Expr := Expr.ident "b"
private def shl (x y : Expr) : Expr := Expr.binary BinaryOp.shl x y

private def u8u8Bytes (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none },
               { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }

-- The submission: `abi.encode(a << b)`.
private def shlFn : ContractItem :=
  u8u8Bytes "f" (abiEncode [Arg.positional (shl a b)])

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [shlFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeShlNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeShlNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeShlNarrow.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeShlNarrow.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n

-- The submission call `f(1, 8)`: `1 << 8` at uint8 truncates to 0 (matches
-- solc+EVM), NOT the un-masked 256 (`0x…0100`) the env-less path encoded.
private def overflowArgs : List Value := [Value.word 1, Value.word 8]
-- SAFE control (byte-identical to the env-less lowering): `1 << 3 = 8` fits in
-- uint8, so `abi.encode(uint8 8)` = the 32-byte word 8.
private def safeArgs : List Value := [Value.word 1, Value.word 3]

def shl_overflow_masks_to_zero : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty overflowArgs (w32 0)
def shl_safe_in_range : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty safeArgs (w32 8)

#guard accepted
#guard isOkTrue shl_overflow_masks_to_zero
#guard isOkTrue shl_safe_in_range

end AbiEncodeShlNarrow
end Witness
end Solidity
end SolidCore

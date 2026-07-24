import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-BITAND-NARROW (S, narrow-add-under-bitand-in-abiencode-arg) — a
BITWISE (`&`/`|`/`^`) expression used as an `abi.encode` argument, whose bitwise
operand carries narrow (`uintN`, N < 256) CHECKED arithmetic.

`return abi.encode((a + b) & 255)` with `uint8 a = 200, b = 100`: solc computes
`a + b` at the operands' common type (uint8) BEFORE the mask, so the addition
overflows (300 > 255) and the call reverts Panic(0x11) BEFORE the `& 255` runs.
solidity-lean lowered the `abi.encode` argument through the env-LESS path
(`Expr.toAbiEncodeArg?` → `Expr.toCore?`), which does NOT thread the type env
into the bitwise operand, so `a + b` ran at 256 bits (`300 & 255 = 44`) and the
call returned `abi.encode(44) = 0x…2c` successfully — a soundness gap
(revert-vs-success).

The fix adds `&`/`|`/`^` arms to the reroute predicate
`Expr.abiArgNeedsEnvCleanupFuel?` (they fire only when an operand itself needs
the cleanup), so such an argument routes through the env-aware recursion
(`Expr.toCoreAsWithEnvFuel?`), whose binary arm lowers each operand at its own
common width (`binaryToCoreWithEnvTypedFuel?`, `_` case) and fires the
operand-width Panic 0x11. A bitwise op with no narrow arithmetic stays
byte-identical (safe controls below).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeBitAndNarrow

open SolidCore.Solidity.Source

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def add (x y : Expr) : Expr := Expr.binary BinaryOp.add x y
private def a : Expr := Expr.ident "a"
private def b : Expr := Expr.ident "b"

private def u8u8Bytes (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none },
               { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }

-- The submission: `abi.encode((a + b) & 255)`.
private def andFn : ContractItem :=
  u8u8Bytes "f" (abiEncode [Arg.positional
    (Expr.binary BinaryOp.bitAnd (add a b) (lit "255"))])

-- `|`-family sibling: `abi.encode((a + b) | 0)`.
private def orFn : ContractItem :=
  u8u8Bytes "fOr" (abiEncode [Arg.positional
    (Expr.binary BinaryOp.bitOr (add a b) (lit "0"))])

-- `^`-family sibling: `abi.encode((a + b) ^ 0)`.
private def xorFn : ContractItem :=
  u8u8Bytes "fXor" (abiEncode [Arg.positional
    (Expr.binary BinaryOp.bitXor (add a b) (lit "0"))])

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [andFn, orFn, xorFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeBitAndNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeBitAndNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeBitAndNarrow.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeBitAndNarrow.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n

-- overflow: 200 + 100 = 300 > 255 -> Panic 0x11 (matches solc+EVM), NOT the
-- env-less `300 & 255 = 44` success.
private def overflowArgs : List Value := [Value.word 200, Value.word 100]
private def safeArgs : List Value := [Value.word 1, Value.word 2]

def and_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "f" State.empty overflowArgs 17
def or_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "fOr" State.empty overflowArgs 17
def xor_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "fXor" State.empty overflowArgs 17

-- SAFE controls (byte-identical to the env-less lowering): 1 + 2 = 3, no
-- overflow. `3 & 255 = 3`, `3 | 0 = 3`, `3 ^ 0 = 3` -> abi.encode(3).
def and_safe_3 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty safeArgs (w32 3)
def or_safe_3 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "fOr" State.empty safeArgs (w32 3)
def xor_safe_3 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "fXor" State.empty safeArgs (w32 3)

#guard accepted
#guard isOkTrue and_overflow_panics
#guard isOkTrue or_overflow_panics
#guard isOkTrue xor_overflow_panics
#guard isOkTrue and_safe_3
#guard isOkTrue or_safe_3
#guard isOkTrue xor_safe_3

end AbiEncodeBitAndNarrow
end Witness
end Solidity
end SolidCore

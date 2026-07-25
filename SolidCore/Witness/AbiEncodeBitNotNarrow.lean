import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-BITNOT-NARROW (S, narrow-bitnot-mask-in-abiencode-arg) — a narrow
(`uintN`/`intN`, N < 256) bitwise NOT `~a` used directly as an `abi.encode`
argument.

`return abi.encode(~a)` with `uint8 a = 1`: solc types the `~` at the operand
width (`uint8`) and cleans the result with `cleanup_t_uint8`
(`and(not(a),0xff)` — a TRUNCATING cast, NOT a range check; `~` never
overflow-panics, even in a checked block), so `not(1) = 0xff…fe` truncates to
`0xfe = 254` and `abi.encode(uint8 254)` = the 32-byte word `254`. solidity-lean
lowered the `abi.encode` argument through the env-LESS path
(`Expr.toAbiEncodeArg?` → `Expr.toCore?`). `annotateAbi` wraps the argument in
the redundant narrow cast `uint8(~a)` (the operand type it recovers WITH the
env), but the env-less cast lowering DROPS that cast when it cannot env-lessly
type the `~` operand (parameter/local idents have no `Expr.abiTy?` arm), leaving
a bare 256-bit `bitNot`. So `~1 = 0xff…fe = 2^256-2` was encoded — a wrong-value
soundness gap.

The fix adds `Expr.peelToNarrowBitNot?` to the reroute predicate
`Expr.abiArgNeedsEnvCleanupFuel?` (it peels the redundant narrow cast to reach
the `~`), so the argument routes through the env-aware recursion, whose Direct
fallback (`Expr.toCoreAs?`) fires `implicitCleanupCore?`'s truncating `uintCast`
for a narrow-uint `~` at the operand width. A word-width (`uint256`) `~` needs no
mask and stays byte-identical (control below).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeBitNotNarrow

open SolidCore.Solidity.Source

private def abiEncode (args : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode") args
private def a : Expr := Expr.ident "a"
private def bitNot (x : Expr) : Expr := Expr.unary UnaryOp.bitNot x

private def u8u8Bytes (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none },
               { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }

-- The submission: `abi.encode(~a)`.
private def bitNotFn : ContractItem :=
  u8u8Bytes "f" (abiEncode [Arg.positional (bitNot a)])

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [bitNotFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeBitNotNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeBitNotNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeBitNotNarrow.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeBitNotNarrow.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n

-- The submission call `f(1, 0)`: `~a` at uint8 masks `not(1) = 0xff…fe` to
-- `0xfe = 254` (matches solc+EVM), NOT the un-masked `2^256-2` (`0xff…fe`) the
-- env-less path encoded. (`b = 0` is unused.)
private def submissionArgs : List Value := [Value.word 1, Value.word 0]
-- A second narrow point: `~0 = 0xff = 255` at uint8.
private def zeroArgs : List Value := [Value.word 0, Value.word 0]

def bitnot_narrow_masks : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty submissionArgs (w32 254)
def bitnot_narrow_zero : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty zeroArgs (w32 255)

#guard accepted
#guard isOkTrue bitnot_narrow_masks
#guard isOkTrue bitnot_narrow_zero

end AbiEncodeBitNotNarrow
end Witness
end Solidity
end SolidCore

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODE-COMPARISON-NARROW (S, narrow-add-comparison-in-abiencode-arg) — a
COMPARISON (or `&&`/`||`/`!` combinator over one) used as an `abi.encode`
argument, whose comparison operand carries narrow (`uintN`, N < 256) CHECKED
arithmetic.

`return abi.encode(a + b > 5)` with `uint8 a = 200, b = 100`: solc evaluates
`a + b` at uint8 while computing the comparison, so the addition overflows
(300 > 255) and the call reverts Panic(0x11) BEFORE the comparison yields a
bool. solidity-lean lowered the `abi.encode` argument through the env-LESS path
(`Expr.toAbiEncodeArg?` → `Expr.toCore?`), which does NOT thread the type env
into the comparison operand, so `a + b` ran at 256 bits (`300 > 5 = true`) and
the call returned `abi.encode(true) = 0x…01` successfully — a soundness gap
(revert-vs-success).

The fix adds comparison / `&&` / `||` / `!` arms to the reroute predicate
`Expr.abiArgNeedsEnvCleanupFuel?` (they fire only when an operand itself needs
the cleanup), so such an argument routes through the env-aware recursion
(`Expr.toCoreAsWithEnvFuel?`), whose comparison / boolean arms lower each
operand at its own width (`binaryToCoreWithEnvTypedFuel?`) and fire the
operand-width Panic 0x11. A comparison with no narrow arithmetic stays
byte-identical (safe controls below).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeComparisonNarrow

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

-- The submission: `abi.encode(a + b > 5)`.
private def gtFn : ContractItem :=
  u8u8Bytes "f" (abiEncode [Arg.positional
    (Expr.binary BinaryOp.gt (add a b) (lit "5"))])

-- `&&`-combinator over the narrow comparison: `abi.encode((a + b > 5) && true)`.
private def andFn : ContractItem :=
  u8u8Bytes "fAnd" (abiEncode [Arg.positional
    (Expr.binary BinaryOp.boolAnd
      (Expr.binary BinaryOp.gt (add a b) (lit "5"))
      (Expr.literal (Literal.bool true)))])

-- `!`-combinator over the narrow comparison: `abi.encode(!(a + b > 5))`.
private def notFn : ContractItem :=
  u8u8Bytes "fNot" (abiEncode [Arg.positional
    (Expr.unary UnaryOp.logicalNot
      (Expr.binary BinaryOp.gt (add a b) (lit "5")))])

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [gtFn, andFn, notFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeComparisonNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeComparisonNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeComparisonNarrow.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeComparisonNarrow.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n

-- overflow: 200 + 100 = 300 > 255 -> Panic 0x11 (matches solc+EVM), NOT success.
private def overflowArgs : List Value := [Value.word 200, Value.word 100]
private def safeArgs : List Value := [Value.word 1, Value.word 2]

def gt_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "f" State.empty overflowArgs 17
def and_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "fAnd" State.empty overflowArgs 17
def not_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "fNot" State.empty overflowArgs 17

-- SAFE controls (byte-identical to the env-less lowering): 1 + 2 = 3, no overflow.
-- `3 > 5 = false` -> abi.encode(false) = 32-byte word 0.
def gt_safe_false : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty safeArgs (w32 0)
-- `(3 > 5) && true = false`.
def and_safe_false : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "fAnd" State.empty safeArgs (w32 0)
-- `!(3 > 5) = true` -> abi.encode(true) = 32-byte word 1.
def not_safe_true : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "fNot" State.empty safeArgs (w32 1)

#guard accepted
#guard isOkTrue gt_overflow_panics
#guard isOkTrue and_overflow_panics
#guard isOkTrue not_overflow_panics
#guard isOkTrue gt_safe_false
#guard isOkTrue and_safe_false
#guard isOkTrue not_safe_true

end AbiEncodeComparisonNarrow
end Witness
end Solidity
end SolidCore

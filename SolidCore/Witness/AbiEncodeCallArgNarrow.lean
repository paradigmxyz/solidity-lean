import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODECALL-ARG-NARROW (S, narrow-add-abi-encodecall-arg) — a narrow
(`uintN`, N < 256) CHECKED arithmetic operand used inside the argument tuple of
`abi.encodeCall`.

`return abi.encodeCall(this.g, (a + b))` with `uint8 a = 200, b = 100` and
`g(uint8)`: solc evaluates `a + b` at uint8 while building the encodeCall
argument tuple, so the addition overflows (300 > 255) and the call reverts
Panic(0x11) BEFORE the calldata is assembled. solidity-lean lowered the
`abi.encodeCall` argument through the env-LESS path: `encodeCall` was ABSENT from
the two operand-width-cleanup reroute predicates
(`Expr.abiArgNeedsEnvCleanupFuel?` for a nested `abi.*` arg and
`Expr.abiBuiltinArgsNeedEnvCleanup` for the return/vardecl statement position),
which listed only `encode`/`encodePacked`/`encodeWithSelector`/
`encodeWithSignature`. So `a + b` ran at 256 bits (300) and the call returned the
encoded calldata `0xab088fbd…012c` successfully — a soundness gap
(revert-vs-success).

The fix adds an `encodeCall` arm to both reroute predicates (inspecting the
argument tuple items), so such an argument routes through the env-aware
recursion (`Expr.toCoreAsWithEnvFuel?`), whose `encodeCall` arm lowers each tuple
item at its own width (`TupleItems.toAbiEncodeSourceWithEnvFuel?`) and fires the
operand-width Panic 0x11. An encodeCall with no narrow arithmetic stays
byte-identical (safe control below).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeCallArgNarrow

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def add (x y : Expr) : Expr := Expr.binary BinaryOp.add x y
private def a : Expr := Expr.ident "a"
private def b : Expr := Expr.ident "b"

-- `g(uint8 x) public pure returns (uint8) { return x; }` — the encodeCall
-- callee. `this.g` names it as an external function pointer.
private def gFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "g",
    visibility := some Visibility.public_, mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) }

-- `abi.encodeCall(this.g, (a + b))` — the submission body. The argument tuple is
-- a one-element tuple carrying the narrow checked addition.
private def encodeCallExpr (argExpr : Expr) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
    [ Arg.positional (Expr.member (Expr.ident "this") "g")
    , Arg.positional (Expr.tuple [TupleItem.value argExpr]) ]

private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.external_, mutability := StateMutability.view,
    params := [{ name := some "a", ty := Ty.uint 8, location := none },
               { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (encodeCallExpr (add a b)))]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [gFn, fFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiEncodeCallArgNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeCallArgNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeCallArgNarrow.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeCallArgNarrow.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def overflowArgs : List Value := [Value.word 200, Value.word 100]
private def safeArgs : List Value := [Value.word 1, Value.word 2]

-- overflow: 200 + 100 = 300 > 255 -> Panic 0x11 (matches solc+EVM), NOT success.
def overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "f" State.empty overflowArgs 17

-- SAFE control (byte-identical to the env-less lowering): 1 + 2 = 3, no overflow.
-- `abi.encodeCall(this.g, (3))` = g's selector (`g(uint8)` = 0xab088fbd) ++ the
-- 32-byte word 3.
private def gSelectorBytes : List Nat :=
  wordToBytesBE selectorBytes (ABI.selectorFromSignature "g(uint8)")
def safe_encodes : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 C "f" State.empty safeArgs
    (gSelectorBytes ++ wordToBytesBE 32 3)

#guard accepted
#guard isOkTrue overflow_panics
#guard isOkTrue safe_encodes

end AbiEncodeCallArgNarrow
end Witness
end Solidity
end SolidCore

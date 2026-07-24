import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-ENCODECALL-NARROW-ARG (S, narrow-add-abi-encodecall-arg) — narrow
(`uintN`, N < 256) CHECKED arithmetic used as an `abi.encodeCall` ARGUMENT
(inside the argument tuple).

`return abi.encodeCall(this.g, (a + b))` with `uint8 a = 200, b = 100` and
`function g(uint8)`: solc evaluates `a + b` at uint8 while building the
argument tuple, so the checked add overflows (300 > 255) and the call reverts
Panic(0x11) BEFORE the calldata is encoded. solidity-lean lowered the
`abi.encodeCall` argument tuple through the env-LESS path
(`TupleItems.toAbiEncodeSource?` → `Expr.toCore?`), which does NOT thread the
type env into the tuple item, so `a + b` ran at 256 bits (300) and the call
returned the encoded calldata `selector(g(uint8)) ++ word(300)` successfully —
a soundness gap (revert-vs-success).

Root cause: the two `abi.encode*` REROUTE predicates that send a statement /
nested argument through the env-aware, operand-width-cleanup lowering
(`Expr.abiBuiltinArgsNeedEnvCleanup`, statement side, and
`Expr.abiArgNeedsEnvCleanupFuel?`, nested-argument side) both listed
`encode`/`encodePacked`/`encodeWithSelector`/`encodeWithSignature` but NOT
`encodeCall`. Without the reroute, `return abi.encodeCall(...)` bottomed out in
the env-LESS `Stmt.toCore?`, so the env-aware `encodeCall` arm (which lowers
each argument-tuple item at its own width via
`TupleItems.toAbiEncodeSourceWithEnvFuel?` and fires the operand-width
Panic 0x11) was DEAD. The fix adds an `encodeCall` arm to BOTH predicates that
peels the argument tuple and flags it when any item itself needs the cleanup;
it fires only then, so an `encodeCall` with no narrow arithmetic stays
byte-identical (safe control below).

Real-EVM ground truth: `f(200,100)` reverts Panic(0x11); `f(1,2)` returns
`selector(g(uint8)) ++ word(3)` = `0xab088fbd…0003`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiEncodeCallNarrowArg

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def add (x y : Expr) : Expr := Expr.binary BinaryOp.add x y
private def a : Expr := Expr.ident "a"
private def b : Expr := Expr.ident "b"

-- `function g(uint8 x) public pure returns (uint8) { return x; }`
private def gFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "g",
    visibility := some Visibility.public_, mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) }

-- `abi.encodeCall(this.g, (a + b))`
private def encodeCallExpr : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
    [ Arg.positional (Expr.member (Expr.ident "this") "g")
    , Arg.positional (Expr.tuple [TupleItem.value (add a b)]) ]

-- `function f(uint8 a, uint8 b) external view returns (bytes memory)`
private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.external_, mutability := StateMutability.view,
    params := [{ name := some "a", ty := Ty.uint 8, location := none },
               { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some encodeCallExpr)]) }

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

end AbiEncodeCallNarrowArg
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeCallNarrowArg

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.AbiEncodeCallNarrowArg.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiEncodeCallNarrowArg.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n

-- The `g(uint8)` selector: 0xab088fbd (matches the adjudicator's observable).
private def gSelector : List Nat := [0xab, 0x08, 0x8f, 0xbd]

private def overflowArgs : List Value := [Value.word 200, Value.word 100]
private def safeArgs : List Value := [Value.word 1, Value.word 2]

-- overflow: 200 + 100 = 300 > 255 -> Panic 0x11 (matches solc+EVM), NOT the
-- 256-bit `selector ++ word(300)` success the env-less path returned.
def overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "f" State.empty overflowArgs 17

-- SAFE control (byte-identical to the env-less lowering): 1 + 2 = 3, no
-- overflow -> `selector(g(uint8)) ++ word(3)`.
def safe_encodes : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 300 C "f" State.empty safeArgs (gSelector ++ w32 3)

#guard accepted
#guard isOkTrue overflow_panics
#guard isOkTrue safe_encodes

end AbiEncodeCallNarrowArg
end Witness
end Solidity
end SolidCore

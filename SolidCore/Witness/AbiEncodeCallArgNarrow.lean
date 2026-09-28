import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Checked narrow arithmetic in `abi.encodeCall` must run at the operand's type
width before calldata encoding. With uint8 arguments 200 and 100, `a + b`
reverts Panic(0x11); arguments 1 and 2 encode normally.

Solc's imported singleton `(a + b)` is a plain expression, not `Expr.tuple`.
The original tuple-only cleanup routing and witness therefore missed the real
submission. Cover both the imported plain-expression form and the original
hand-built singleton tuple. Routing and env-aware lowering support both forms.
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
-- importer unwraps its parentheses; the actual argument is a plain expression.
private def encodeCallExpr (tupleForm : Bool) (argExpr : Expr) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
    [ Arg.positional (Expr.member (Expr.ident "this") "g")
    , Arg.positional (if tupleForm then Expr.tuple [TupleItem.value argExpr] else argExpr) ]

private def fFn (tupleForm : Bool) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.external_, mutability := StateMutability.view,
    params := [{ name := some "a", ty := Ty.uint 8, location := none },
               { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (encodeCallExpr tupleForm (add a b)))]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [gFn, fFn false] }

def tupleContract : ContractDecl :=
  { importedContractDecl0 with items := [gFn, fFn true] }

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

-- Keep the original hand-built tuple control alongside the actual importer form.
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 300
  SolcAstImport.AbiEncodeCallArgNarrow.tupleContract "f" State.empty overflowArgs 17)
#guard isOkTrue (Examples.checkedOwnCallBytesMatches 256
  SolcAstImport.AbiEncodeCallArgNarrow.tupleContract "f" State.empty safeArgs
  (gSelectorBytes ++ wordToBytesBE 32 3))

end AbiEncodeCallArgNarrow
end Witness
end Solidity
end SolidCore

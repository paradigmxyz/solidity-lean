import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TUPLE-RHS-STORAGE-BYTES (#192 family) — a BARE STATE `bytes` variable used as a
COMPONENT of a value-position tuple RHS, copied into a memory local:

```solidity
contract C {
    bytes src;
    function run() external returns (uint256) {
        src.push(0x11); src.push(0x22);
        (bytes memory b, uint256 x) = (src, uint256(5));
        return b.length * 100 + x * 10 + uint256(uint8(b[1]) / 16);
    }
}
```

The tuple RHS `(src, 5)` reads each component by value: `b` is a fresh memory
`bytes` bound to a COPY of the storage `bytes` contents. solc+EVM copies the
storage `bytes` to memory here, so `b.length == 2`, `b[1] == 0x22`, and `run()`
returns `2*100 + 5*10 + (0x22/16) = 200 + 50 + 2 = 252`.

solidity-lean formerly REVERTED with `Panic(0)`: the value-position tuple arm of
`Expr.toCore?` lowered each component with `TupleItems.toCoreExprs?` WITHOUT
materializing, so the bare state `bytes` `src` lowered to `Expr.storage key` (the
storage HEADER word, the `.length` convention = `2*len+1`). Binding the memory
local `b` to that word fed a non-`bytes` `Value.word` to the copy boundary →
`asBytes?` = `none` → `RevertData.typeMismatch` = `Panic(0)`.

The fix materializes each tuple component in that arm (`Expr.storage key` →
`Expr.storagePath key []`, via `materializeStorageValueUseCores`), matching the
other value-use boundaries (#4 abi.decode data arg, #5 ternary branches). Scalar
components (`uint256(5)`) load identically and are unaffected.

Real-EVM ground truth (adjudicated divergence): `run()` => `success|w:252`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleRhsStorageBytes

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def u256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]
private def u8 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional e]

-- `src = hex"1122";` (contents equivalent to `src.push(0x11); src.push(0x22);`)
private def setSrc : Stmt :=
  Stmt.expr (Expr.assign (Expr.ident "src") AssignOp.assign
    (Expr.literal (Literal.hexString "1122")))

-- `(bytes memory b, uint256 x) = (src, uint256(5));`
private def tupleDecl : Stmt :=
  Stmt.varDecl
    [ { name := some "b", ty := some Ty.bytes, location := some DataLocation.memory }
    , { name := some "x", ty := some (Ty.uint 256), location := none } ]
    (some (Expr.tuple
      [ TupleItem.value (Expr.ident "src")
      , TupleItem.value (u256 (lit "5")) ]))

-- `return b.length * 100 + x * 10 + uint256(uint8(b[1]) / 16);`
private def retExpr : Expr :=
  Expr.binary BinaryOp.add
    (Expr.binary BinaryOp.add
      (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "b") "length") (lit "100"))
      (Expr.binary BinaryOp.mul (Expr.ident "x") (lit "10")))
    (u256 (Expr.binary BinaryOp.div
      (u8 (Expr.index (Expr.ident "b") (lit "1")))
      (lit "16")))

private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ setSrc, tupleDecl
        , Stmt.returnValues (some retExpr) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "src", ty := Ty.bytes }, runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleRhsStorageBytes
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleRhsStorageBytes

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.TupleRhsStorageBytes.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TupleRhsStorageBytes.importedContractAccepted

-- The divergence witness: `run()` returns `252`, matching solc+EVM (pre-fix this
-- reverted with `Panic(0)` at the tuple-decl copy and yielded `false`).
def run_tuple_rhs_bytes_is_252 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "run" State.empty [] 252

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_tuple_rhs_bytes_is_252

end TupleRhsStorageBytes
end Witness
end Solidity
end SolidCore

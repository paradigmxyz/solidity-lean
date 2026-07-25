import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
BYTES-OF-STRING-STORAGE-BYTE-WRITE (divergence): writing a single byte through a
`bytes(...)` REINTERPRET of a *storage* `string` lvalue —

  string s = "abc";
  function run() public returns (uint256) {
    bytes(s)[0] = 0x41;                 // 'a'(0x61) -> 'A'(0x41)
    return uint256(uint8(bytes(s)[0])); // 0x41 = 65
  }

Real solc 0.8.35 + EVM ground truth: `bytes(s)` is a pointer reinterpret of the
storage `string s` (identical length-prefixed layout), so `bytes(s)[0]` is an
assignable storage byte. Writing 0x41 rewrites the first content byte; `run()`
returns 65 and storage slot 0 becomes `0x4162630…06` ("Abc", short-string
header 2*3 = 6).

The bug: the assignment-target lvalue `bytes(s)[0]` peels the reinterpret to a
storage index write (`LValue.index (LValue.storage s) 0`), but the interpreter's
storage index-write dispatch (`Runtime.storeStorageIndex` /
`…WithDeepClear`) hard-rejected the `StorageLayout.string` field with
`RevertData.typeMismatch` = Panic(0) — solidity-lean reverted where solc
succeeds. Direct `s[i] = v` on a `string` is rejected by the typechecker, so a
`string` field reaches the storage byte-write dispatch ONLY via the `bytes(s)`
reinterpret; treating it exactly like a `bytes` field (same layout,
`storeStorageByteAt`) is the fix.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace BytesOfStringStorageByteWrite

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

-- bytes(<ident>) as an expression
private def bytesOf (name : String) : Expr :=
  Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.ident name)]

-- s = "abc";
private def assignS : Stmt :=
  Stmt.expr (Expr.assign (Expr.ident "s") AssignOp.assign
    (Expr.literal (Literal.string "abc")))

-- bytes(s)[0] = 0x41;
private def mutateS : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.index (bytesOf "s") (Expr.literal (Literal.number "0")))
    AssignOp.assign
    (Expr.literal (Literal.number "0x41")))

-- return uint256(uint8(bytes(s)[0]));
private def retStmt : Stmt :=
  Stmt.returnValues (some
    (Expr.call (Expr.typeName (Ty.uint 256))
      [Arg.positional
        (Expr.call (Expr.typeName (Ty.uint 8))
          [Arg.positional
            (Expr.index (bytesOf "s") (Expr.literal (Literal.number "0")))])]))

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "s", ty := Ty.string, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.public_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block [assignS, mutateS, retStmt]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

#guard accepted

private def word (n : Nat) : List Byte := List.replicate 31 0 ++ [n]

-- Expected ABI return data: uint256 65.
def expectedOutput : List Byte := word 65

def runMatches : Except TypeError Bool :=
  Examples.checkedContractAbiOutputMatches 4096 runContract "run" [] (some expectedOutput)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

-- Storage slot 0 after the write: "Abc" short string = 0x4162630…06.
def storageMatches : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run"
    SolidCore.Solidity.Source.State.empty []
  Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
    0x4162630000000000000000000000000000000000000000000000000000000006)

#guard isOkTrue runMatches
#guard isOkTrue storageMatches

end BytesOfStringStorageByteWrite
end Witness
end Solidity
end SolidCore

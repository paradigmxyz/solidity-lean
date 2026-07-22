import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
EMIT-REVERT-NESTED-ENV (soundness, adjudicated x2) — witnesses for the two
emit/revert lowering fixes landed together with the SS3c emit/revert collapse
(`FunctionDecl.eventErrorCallArgsCore?`).

(1) NESTED-DYNAMIC CALL PAYLOADS. The two-internal-call shapes

```solidity
error Nested(uint256[][] a, string b);
function mk() internal pure returns (uint256[][] memory m) { m = new uint256[][](1); m[0] = new uint256[](1); m[0][0] = 4; }
function sk() internal pure returns (string memory) { return "qq"; }
function go() external pure { revert Nested(mk(), sk()); }        // revert channel
// event N2(uint256[][] m, uint256 k);  emit N2(mk(), f2());       // emit channel
// return (mk(), f2());                                            // return channel
```

formerly rendered `Panic(0)` on the revert/emit channels where solc+EVM
produce the fully ABI-encoded custom error / event: the two-call hoist
helper parked the first return in a plain `Stmt.varDecl` temp, whose eval
shallow-derefs and runs `Ty.coerceValue?`, which has no case for the
`Value.memoryRef` rows nested INSIDE the aggregate -> `typeMismatch` =
Panic(0). Fixed by `CoreTy.tempDeclStmt`: aggregate-typed lowering temps are
declared with the pointer-aliasing `Stmt.memoryVarDecl` (a memory-to-memory
bind is a pointer copy on the EVM). The byte-level ground truth is pinned
against the real EVM in the forge lanes `revert-nested-two-call` /
`emit-nested-two-call`; here the revert payload is additionally encoded via
`Contract.encodeRevertData?` and compared to the exact solc ABI bytes
(`cast abi-encode` cross-checked).

(2) MIXED-SHAPE REVERT ENV-CLEANUP (#201 E completion).

```solidity
error Err(uint8 s, uint256 k);
uint256 c;
function bump() internal returns (uint256) { c += 1; return c; }
function run(uint8 a, uint8 b) external { revert Err(a + b, bump()); }
```

`run(200, 100)`: solc evaluates the error arguments BEFORE reverting, so the
narrow checked `a + b` overflows uint8 and Panics 0x11. The revert lowering
arms were emit copy-paste that had drifted env-less (`Expr.toCore?`), so the
model encoded `Err(300, 1)`. Both channels now route the pure companion
arguments through `Expr.abiArgCoreWithEnvCleanup?` in the shared helper.
Controls: `run(2, 3)` still reverts `Err(5, 1)` (hoisted `bump()` runs), and
the call-free `revert Err(a + b)` keeps its catch-all env-cleanup Panic 0x11.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RevertNestedTwoCall

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "V10"
  abstract := false
  bases := []
  items := [(ContractItem.errorDecl
  { name := "Nested",
    params := [{ name := some "a", ty := Ty.array (Ty.array (Ty.uint 256) (none)) (none), location := none }, { name := some "b", ty := Ty.string, location := none }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mk",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := some "m", ty := Ty.array (Ty.array (Ty.uint 256) (none)) (none), location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "m") AssignOp.assign (Expr.newExpr (Ty.array (Ty.array (Ty.uint 256) (none)) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "4")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sk",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.string, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.string "qq")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "go",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.ident "Nested") [Arg.positional (Expr.call (Expr.ident "mk") []), Arg.positional (Expr.call (Expr.ident "sk") [])])]) })] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RevertNestedTwoCall
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EmitNestedTwoCall

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "V27"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "N2",
    params := [{ name := some "m", ty := Ty.array (Ty.array (Ty.uint 256) (none)) (none), indexed := false }, { name := some "k", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mk",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := some "m", ty := Ty.array (Ty.array (Ty.uint 256) (none)) (none), location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "m") AssignOp.assign (Expr.newExpr (Ty.array (Ty.array (Ty.uint 256) (none)) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "4")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f2",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "9")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "go",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "N2") [Arg.positional (Expr.call (Expr.ident "mk") []), Arg.positional (Expr.call (Expr.ident "f2") [])])]) })] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EmitNestedTwoCall
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ReturnNestedTwoCall

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "V28"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "mk",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := some "m", ty := Ty.array (Ty.array (Ty.uint 256) (none)) (none), location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "m") AssignOp.assign (Expr.newExpr (Ty.array (Ty.array (Ty.uint 256) (none)) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "4")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f2",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "9")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "go",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.array (Ty.array (Ty.uint 256) (none)) (none), location := some DataLocation.memory }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.call (Expr.ident "mk") []), TupleItem.value (Expr.call (Expr.ident "f2") [])]))]) })] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ReturnNestedTwoCall
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RevertMixedEnvCleanup

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Bug2"
  abstract := false
  bases := []
  items := [(ContractItem.errorDecl
  { name := "Err",
    params := [{ name := some "s", ty := Ty.uint 8, location := none }, { name := some "k", ty := Ty.uint 256, location := none }] }), (ContractItem.stateVar
  { name := "c",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "c") AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "c"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.ident "Err") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), Arg.positional (Expr.call (Expr.ident "bump") [])])]) })] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RevertMixedEnvCleanup
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RevertCallFreeEnvCleanup

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C1"
  abstract := false
  bases := []
  items := [(ContractItem.errorDecl
  { name := "Err",
    params := [{ name := some "s", ty := Ty.uint 8, location := none }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.ident "Err") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]) })] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RevertCallFreeEnvCleanup
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EmitRevertNestedEnv

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def w (n : Nat) : List Byte :=
  SolidCore.Solidity.Source.wordToBytesBE 32 n

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

-- ---------------------------------------------------------------------------
-- (1a) REVERT channel: revert Nested(mk(), sk()) with nested-dynamic mk().
-- ---------------------------------------------------------------------------

abbrev RevertFam :=
  SolidCore.Solidity.SolcAstImport.RevertNestedTwoCall.importedContract

-- abi bytes of Nested([[4]], "qq"): selector 0xb62a1a94 ++
-- head(m=0x40, s=0xc0) ++ m payload(len 1, row off 0x20, row len 1, 4) ++
-- s payload(len 2, "qq" right-padded). Cross-checked with
-- `cast abi-encode "f(uint256[][],string)" "[[4]]" "qq"`.
private def expectedNestedRevertBytes : List Byte :=
  [0xb6, 0x2a, 0x1a, 0x94] ++
    w 0x40 ++ w 0xc0 ++
    w 1 ++ w 0x20 ++ w 1 ++ w 4 ++
    w 2 ++ ([0x71, 0x71] ++ List.replicate 30 0)

def revert_nested_two_call_materializes : Except TypeError Bool := do
  let result <-
    CheckedInput.ownCall 64 RevertFam
      (SolidCore.Solidity.Source.CallTarget.name "go")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _ rd =>
      -- Structural check: the payload values are FULLY materialized (no
      -- memoryRef leaves) -- pre-fix this was `RevertData.panic 0`.
      let structural :=
        match rd with
        | RevertData.custom "Nested"
            [ Value.dynamicArray [Value.dynamicArray [Value.word row]]
            , Value.bytes [0x71, 0x71] ] => row == 4
        | _ => false
      -- Byte check: the encoded revert data equals the solc/EVM ABI bytes.
      let encoded :=
        match SolidCore.Solidity.Executable.ContractDecl.toCoreWithBases?
            [RevertFam] RevertFam with
        | some core =>
            SolidCore.Solidity.Source.ABI.Contract.encodeRevertData?
                core rd ==
              some expectedNestedRevertBytes
        | none => false
      Except.ok (structural && encoded)
  | _ => Except.ok false

-- ---------------------------------------------------------------------------
-- (1b) EMIT channel: emit N2(mk(), f2()).
-- ---------------------------------------------------------------------------

abbrev EmitFam :=
  SolidCore.Solidity.SolcAstImport.EmitNestedTwoCall.importedContract

-- abi.encode([[4]], 9): head(m=0x40) ++ 9 ++ m payload(len 1, row off 0x20,
-- row len 1, 4). Cross-checked with
-- `cast abi-encode "f(uint256[][],uint256)" "[[4]]" 9`.
private def expectedEmitDataBytes : List Byte :=
  w 0x40 ++ w 9 ++ w 1 ++ w 0x20 ++ w 1 ++ w 4

def emit_nested_two_call_materializes : Except TypeError Bool := do
  let result <-
    CheckedInput.ownCall 64 EmitFam
      (SolidCore.Solidity.Source.CallTarget.name "go")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "N2" &&
              event.topics ==
                [SolidCore.Solidity.Source.Keccak.digestWord
                  "N2(uint256[][],uint256)"] &&
              event.dataBytes == expectedEmitDataBytes)
      | _ => Except.ok false
  | _ => Except.ok false

-- ---------------------------------------------------------------------------
-- (1c) RETURN channel control: return (mk(), f2()) stays materialized.
-- ---------------------------------------------------------------------------

abbrev ReturnFam :=
  SolidCore.Solidity.SolcAstImport.ReturnNestedTwoCall.importedContract

def return_nested_two_call_materializes : Except TypeError Bool := do
  let result <-
    CheckedInput.ownCall 64 ReturnFam
      (SolidCore.Solidity.Source.CallTarget.name "go")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ values =>
      match values with
      | [ Value.dynamicArray [Value.dynamicArray [Value.word row]]
        , Value.word k ] => Except.ok (row == 4 && k == 9)
      | _ => Except.ok false
  | _ => Except.ok false

-- ---------------------------------------------------------------------------
-- (2) revert Err(a + b, bump()) -- narrow checked arithmetic Panics 0x11.
-- ---------------------------------------------------------------------------

abbrev MixedFam :=
  SolidCore.Solidity.SolcAstImport.RevertMixedEnvCleanup.importedContract

def mixed_revert_overflow_panics_0x11 : Except TypeError Bool := do
  let result <-
    CheckedInput.ownCall 64 MixedFam
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [Value.word 200, Value.word 100]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _ rd =>
      match rd with
      | RevertData.panic code => Except.ok (code == 0x11)
      | _ => Except.ok false
  | _ => Except.ok false

-- Control: no overflow -> the custom error with the hoisted bump() value.
def mixed_revert_no_overflow_control : Except TypeError Bool := do
  let result <-
    CheckedInput.ownCall 64 MixedFam
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [Value.word 2, Value.word 3]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _ rd =>
      match rd with
      | RevertData.custom "Err" [Value.word s, Value.word k] =>
          Except.ok (s == 5 && k == 1)
      | _ => Except.ok false
  | _ => Except.ok false

-- Control: call-free revert Err(a + b) keeps the catch-all env cleanup.
abbrev CallFreeFam :=
  SolidCore.Solidity.SolcAstImport.RevertCallFreeEnvCleanup.importedContract

def callfree_revert_overflow_panics_0x11 : Except TypeError Bool := do
  let result <-
    CheckedInput.ownCall 64 CallFreeFam
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [Value.word 200, Value.word 100]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _ rd =>
      match rd with
      | RevertData.panic code => Except.ok (code == 0x11)
      | _ => Except.ok false
  | _ => Except.ok false

#guard SolidCore.Solidity.SolcAstImport.RevertNestedTwoCall.importedContractAccepted
#guard SolidCore.Solidity.SolcAstImport.EmitNestedTwoCall.importedContractAccepted
#guard SolidCore.Solidity.SolcAstImport.ReturnNestedTwoCall.importedContractAccepted
#guard SolidCore.Solidity.SolcAstImport.RevertMixedEnvCleanup.importedContractAccepted
#guard SolidCore.Solidity.SolcAstImport.RevertCallFreeEnvCleanup.importedContractAccepted
#guard isOkTrue revert_nested_two_call_materializes
#guard isOkTrue emit_nested_two_call_materializes
#guard isOkTrue return_nested_two_call_materializes
#guard isOkTrue mixed_revert_overflow_panics_0x11
#guard isOkTrue mixed_revert_no_overflow_control
#guard isOkTrue callfree_revert_overflow_panics_0x11

end EmitRevertNestedEnv
end Witness
end Solidity
end SolidCore

/-
In-file example and demo witness defs relocated out of `Interpreter.lean`
(Phase 6, N3 — de-monolith: examples do not belong in the semantics file).
Moved verbatim, declaration names and `SolidCore.Solidity.Source` namespace
preserved (none are manifest-referenced; verified). Includes the synthetic
`phase5DemoTree`/`phase5DemoTranscriptLength` demo and the statement/expression
example corpus (`compositionalControlExample`, signed-arithmetic, revert/require,
`writesThenReverts`, etc.) with their little AST-builder helpers.
-/
import SolidCore.Solidity.Interpreter
import SolidCore.Solidity.ABI

namespace SolidCore
namespace Solidity
namespace Source

/-- Short witness: a two-external-call execution as an explicit interaction tree;
    `queryTranscript` exposes its two external-call queries. -/
def phase5DemoTree (context : Context) : SolI (List LowLevelCallResult) := do
  let (r1, _) ← emitLowLevelCall context State.empty
    LowLevelCallKind.call 0xa11ce [0x11, 0x22] 0 none
  let (r2, _) ← emitLowLevelCall context State.empty
    LowLevelCallKind.call 0xb0b [0x33] 7 (some 50000)
  pure [r1, r2]

/-- The demo tree emits exactly two external-call queries. -/
def phase5DemoTranscriptLength (context : Context) : Nat :=
  (SolI.queryTranscript 8 (contextAnswer context) (phase5DemoTree context)).length

/-- openworld/postworld Stage 1 witness: the emitted query carries a REAL
    `OpenWorld` snapshot — the self account holds the live storage, transient
    storage, A2 `selfBalance`, `selfNonce`, and Context-seeded code; the log
    series carries the emitted events; `createdAccounts` carries the Context
    seed. Pinned against a non-default state so a regression to the old
    `default` placeholder fails the build (see the `#eval` below). -/
def snapshotWitnessContext : Context :=
  { Context.empty with
    self := 0xcafe
    accountCodes := [(0xcafe, [0xfe, 0xed])]
    accountBalances := [(0xd00d, 55)]
    createdInTransactionAccounts := [0xbeef] }

def snapshotWitnessState : State :=
  { State.empty with
    storage := StorageMap.insertLoop {} 1 42
    transient := StorageMap.insertLoop {} 2 9
    selfBalance := 77
    selfNonce := 3
    events :=
      [{ name := "Ping", indexed := [], data := [],
         topics := [5], dataBytes := [1] }] }

def snapshotWitnessWorld : SolidCore.Solidity.Shared.OpenWorld :=
  snapshotWorld snapshotWitnessContext snapshotWitnessState

def snapshotWitnessMatches : Bool :=
  -- The emitted query's world is exactly `snapshotWorld` of the emit state.
  let emitted :=
    match emitLowLevelCall snapshotWitnessContext snapshotWitnessState
        LowLevelCallKind.call 0xd00d [] 0 none with
    | .request (EvmCompiler.Simulation.Query.external world _) _ =>
        some world
    | _ => none
  match emitted with
  | none => false
  | some world =>
      match world.accounts.find? (wordToAddress 0xcafe) with
      | none => false
      | some self =>
          u256ToWord self.balance == 77 &&
          u256ToWord self.nonce == 3 &&
          (self.storage.find? (wordToU256 1)).map u256ToWord == some 42 &&
          (self.transientStorage.find? (wordToU256 2)).map u256ToWord ==
            some 9 &&
          byteArrayToBytes self.codeBytes == [0xfe, 0xed] &&
          (match world.accounts.find? (wordToAddress 0xd00d) with
           | some other => u256ToWord other.balance == 55
           | none => false) &&
          world.substate.logSeries.size == 1 &&
          world.createdAccounts.contains (wordToAddress 0xbeef)

def uint256 (name : String) : BindingDecl :=
  { name, ty := Ty.uint256 }

def int256 (name : String) : BindingDecl :=
  { name, ty := Ty.int256 }

def bool (name : String) : BindingDecl :=
  { name, ty := Ty.bool }

def address (name : String) : BindingDecl :=
  { name, ty := Ty.address }

def bytesCalldata (name : String) : BindingDecl :=
  { name, ty := Ty.bytesCalldata }

def fixedWordArray (size : Nat) : Ty :=
  Ty.fixedArray size Ty.uint256

def Expr.zero : Expr :=
  Expr.word 0

def Expr.one : Expr :=
  Expr.word 1

def Expr.bytesLiteral (bytes : List Byte) : Expr :=
  Expr.byteArray bytes

def Expr.add (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.add lhs rhs

def Expr.sub (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.sub lhs rhs

def Expr.mul (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.mul lhs rhs

def Expr.div (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.div lhs rhs

def Expr.lt (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.lt lhs rhs

def Expr.eq (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.eq lhs rhs

def Expr.bitAnd (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.bitAnd lhs rhs

def Stmt.seq (stmts : List Stmt) : Stmt :=
  Stmt.block stmts

def compositionalControlExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "x" (some (Expr.word 0))
    , Stmt.whileLoop
        (Expr.lt (Expr.var "x") (Expr.word 4))
        (Stmt.block
          [ Stmt.ifElse
              (Expr.eq
                (Expr.bitAnd (Expr.var "x") (Expr.word 1))
                Expr.zero)
              (Stmt.assignOp (LValue.var "x") BinaryOp.add (Expr.word 2))
              (Stmt.assignOp (LValue.var "x") BinaryOp.add Expr.one)
          ])
    , Stmt.returnValues [Expr.var "x"]
    ]

def compositionalControlResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 20 [] Context.empty (Runtime.ofState State.empty)
      compositionalControlExample)).toOption

def ternarySkipsRejectedBranch : Stmt :=
  Stmt.returnValues
    [ Expr.ternary (Expr.word 1)
        (Expr.word 7)
        (Expr.div (Expr.word 1) (Expr.word 0)) ]

def ternarySkipsRejectedBranchResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 8 [] Context.empty (Runtime.ofState State.empty)
      ternarySkipsRejectedBranch)).toOption

def doWhileRunsBeforeCondition : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "x" (some (Expr.word 0))
    , Stmt.doWhile
        (Stmt.assignOp (LValue.var "x") BinaryOp.add Expr.one)
        (Expr.lt (Expr.var "x") (Expr.word 1))
    , Stmt.returnValues [Expr.var "x"] ]

def doWhileRunsBeforeConditionResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 16 [] Context.empty (Runtime.ofState State.empty)
      doWhileRunsBeforeCondition)).toOption

def expressionStatementFailure : Stmt :=
  Stmt.exprStmt (Expr.div (Expr.word 1) (Expr.word 0))

def expressionStatementFailureResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 4 [] Context.empty (Runtime.ofState State.empty)
      expressionStatementFailure)).toOption

def deleteLocalExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "x" (some (Expr.word 5))
    , Stmt.deleteValue (LValue.var "x")
    , Stmt.returnValues [Expr.var "x"] ]

def deleteLocalResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 8 [] Context.empty (Runtime.ofState State.empty)
      deleteLocalExample)).toOption

def defaultBoolExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.bool "ok" none
    , Stmt.returnValues [Expr.var "ok"] ]

def defaultBoolResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 8 [] Context.empty (Runtime.ofState State.empty)
      defaultBoolExample)).toOption

def signedArithmeticExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.int256 "x"
        (some (Expr.intWord (SolidCore.Solidity.Shared.signedToWord (-5))))
    , Stmt.varDecl Ty.int256 "y" (some (Expr.intWord 2))
    , Stmt.returnValues
        [ Expr.div (Expr.var "x") (Expr.var "y")
        , Expr.binary BinaryOp.mod (Expr.var "x") (Expr.var "y")
        , Expr.lt (Expr.var "x") (Expr.var "y") ] ]

def signedArithmeticResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 12 [] Context.empty (Runtime.ofState State.empty)
      signedArithmeticExample)).toOption

def signedNegOverflowExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.int256 "x"
        (some (Expr.intWord SolidCore.Solidity.Shared.halfWordModulus))
    , Stmt.returnValues [Expr.unary UnaryOp.neg (Expr.var "x")] ]

def signedNegOverflowResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 8 [] Context.empty (Runtime.ofState State.empty)
      signedNegOverflowExample)).toOption

def uncheckedSignedNegWrapExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.int256 "x"
        (some (Expr.intWord SolidCore.Solidity.Shared.halfWordModulus))
    , Stmt.unchecked
        (Stmt.returnValues [Expr.unary UnaryOp.neg (Expr.var "x")]) ]

def uncheckedSignedNegWrapResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 8 [] Context.empty (Runtime.ofState State.empty)
      uncheckedSignedNegWrapExample)).toOption

def assertFailureExample : Stmt :=
  Stmt.assertStmt (Expr.word 0)

def assertFailureResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 4 [] Context.empty (Runtime.ofState State.empty)
      assertFailureExample)).toOption

def requireFailureExample : Stmt :=
  Stmt.requireStmt (Expr.word 0) (some "Nope")

def requireFailureResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 4 [] Context.empty (Runtime.ofState State.empty)
      requireFailureExample)).toOption

def revertStringExample : Stmt :=
  Stmt.revertError (some "Nope")

def revertStringResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 4 [] Context.empty (Runtime.ofState State.empty)
      revertStringExample)).toOption

def captureReturnExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "ret" none
    , Stmt.varDecl Ty.uint256 "x" (some (Expr.word 0))
    , Stmt.captureReturn ["ret"]
        (Stmt.block
          [ Stmt.returnValues [Expr.word 7]
          , Stmt.assign (LValue.var "x") (Expr.word 99) ])
    , Stmt.assign (LValue.var "x") (Expr.word 1)
    , Stmt.returnValues [Expr.var "ret", Expr.var "x"] ]

def captureReturnResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 16 [] Context.empty (Runtime.ofState State.empty)
      captureReturnExample)).toOption

def bytesReturnExample : Stmt :=
  Stmt.returnValues [Expr.byteArray [0x41, 0x42]]

def bytesReturnResult : Option Result :=
  (SolI.run Context.empty
    (Stmt.eval 4 [] Context.empty (Runtime.ofState State.empty)
      bytesReturnExample)).toOption

def rollbackContext : Context :=
  { Context.empty with
    storageFields := [{ name := "x", slot := 0 }] }

def writesThenReverts : FunctionDef :=
  { name := "fail"
    selector? := none
    params := []
    returns := []
    body :=
      Stmt.block
        [ Stmt.assign (LValue.storage "x") (Expr.word 7)
        , Stmt.revert "Nope" [] ] }

def writesThenRevertsCall : Option CallResult :=
  writesThenReverts.call? 8 [writesThenReverts.toInternal] rollbackContext State.empty []

/-! ### DEC-ALLOC-MEMPTR (#114): `abiCheckAllocation?` finalize-allocation band

solc's `finalize_allocation` panics 0x41 when `add(memPtr, roundUp(size))`
exceeds `2^64-1`, with `memPtr` (≥ `0x80`) the running free-memory pointer that
the older raw `elementSize * n + 0x20` bound omitted. These witnesses pin the
band on the reachable `memPtr = 0x80` path and confirm the guard does not
over-panic just below it. -/

-- `uint256[]` (value array). `32 * n + 32 = 2^64 - 32 ≤ 2^64-1`, so the raw
-- bound alone would NOT panic; the `0x80` memPtr base tips it over → Panic(0x41).
example :
    abiCheckAllocation? false 576460752303423486
      = Except.error RevertData.memoryAllocationTooLarge := rfl

-- One below the solc threshold (`32 * n + 32 + 0x80 = 2^64 - 1`): NO over-panic.
example :
    abiCheckAllocation? false 576460752303423482 = Except.ok () := rfl

-- `bytes` (byte array). `n + 32 = 2^64 - 1 ≤ 2^64-1`; raw bound would NOT panic,
-- but `roundUp(n) + 32 + 0x80` overflows `2^64-1` → Panic(0x41).
example :
    abiCheckAllocation? true 18446744073709551583
      = Except.error RevertData.memoryAllocationTooLarge := rfl

-- Isolates the byte-length roundUp: at `n = 2^64 - 161` even `n + 32 + 0x80`
-- (memPtr WITHOUT roundUp) equals exactly `2^64-1` and would NOT panic, but
-- `roundUp(n) = 2^64 - 160` pushes `newFreePtr` to `2^64` → Panic(0x41).
example :
    abiCheckAllocation? true 18446744073709551455
      = Except.error RevertData.memoryAllocationTooLarge := rfl

-- The raw-count first gate still fires above `2^64-1` (unchanged from #62/#88).
example :
    abiCheckAllocation? false (2 ^ 64)
      = Except.error RevertData.memoryAllocationTooLarge := rfl

-- A normal small length is unaffected: no over-panic for either shape.
example : abiCheckAllocation? false 3 = Except.ok () := rfl
example : abiCheckAllocation? true 3 = Except.ok () := rfl

/-! ### ABI-DECODE-EAGER-HEADCHECK (#128): truncated dynamic-element-array head

When solc EAGERLY decodes a `memory` array of dynamically-encoded elements
(`bytes[] memory`, `string[] memory`, `uint[][] memory`, dynamic `S[] memory`,
or `abi.decode(data, (bytes[]))`), `abi_decode_available_length_*_array` emits a
HEAD-AREA presence check — `srcEnd := add(arrayPos, mul(length, 0x20)); if
gt(srcEnd, end) { revert(0,0) }` — AFTER the outer allocation but BEFORE the
element loop. So a truncated outer head reverts EMPTY; solc never reaches an
inner element's allocation. The model previously ran this check only on the
calldata (lazy) path, so on the eager (memory) path it decoded elements
immediately and an inner huge length hit `abiCheckAllocation?` → Panic(0x41),
turning solc's empty revert into a Panic. These witnesses pin the fix.

Calldata (post-selector, relative): outer offset 0x20, length 3, elem0 inner
offset 0x20, then 2^64. arrayPos = 0x40, srcEnd = 0x40 + 3*0x20 = 0xA0 > end =
0x80 → EMPTY. Pre-fix the model reached elem0 whose inner length 2^64 fired
`abiCheckAllocation? true (2^64)` = Panic(0x41) (see the raw-count witness above).

The decoders are fuel-recursive (compiled via `brecOn`), so they do not reduce
under the kernel `rfl` used above; these results are pinned with `#guard`, which
evaluates via the interpreter and fails the build if false, adding no axioms. -/

def word32 (value : Word) : List Byte := wordToBytesBE 32 value

/-- Bool view: the decode reverts EMPTY (solc `revert(0,0)`), not Panic(0x41). -/
def headCheckIsEmptyRevert {α} : Except RevertData α -> Bool
  | Except.error RevertData.empty => true
  | _ => false

/-- Bool view: the decode succeeds (used for the no-over-reject controls). -/
def headCheckDecodeOk {α} : Except RevertData α -> Bool
  | Except.ok _ => true
  | _ => false

-- `bytes[] memory` with a truncated element-head area (srcEnd = 0xA0 > end 0x80).
def truncatedBytesArrayHeadCalldata : List Byte :=
  word32 0x20 ++ word32 3 ++ word32 0x20 ++ word32 (2 ^ 64)

-- External `memory`-param eager path (`ABI.decodeValueAt?`, lazy = false):
-- reverts EMPTY at the head-area check, NOT Panic(0x41).
#guard headCheckIsEmptyRevert
  (ABI.decodeValueAt? false truncatedBytesArrayHeadCalldata 0
    (Ty.dynamicArray Ty.bytesCalldata))

-- `abi.decode(data, (bytes[]))` / external-return eager path
-- (`abiDecodeValuesExcept?`): same EMPTY revert, not Panic(0x41).
#guard headCheckIsEmptyRevert
  (abiDecodeValuesExcept? [Ty.dynamicArray Ty.bytesCalldata]
    truncatedBytesArrayHeadCalldata)

-- Positive control 1: a well-formed `uint[] memory` with `srcEnd == end` (the
-- strict-`gt` boundary) still PASSES and decodes — no over-reject. length 1,
-- arrayPos 0x40, srcEnd 0x40 + 1*0x20 = 0x60 = end.
def wellFormedSrcEndEqEndCalldata : List Byte :=
  word32 0x20 ++ word32 1 ++ word32 42

#guard headCheckDecodeOk
  (ABI.decodeValueAt? false wellFormedSrcEndEqEndCalldata 0
    (Ty.dynamicArray Ty.uint256))

-- Positive control 2: trailing garbage beyond `end` is fine (the head fits;
-- `end` is the actual data end) — still passes and decodes the single element.
def wellFormedTrailingGarbageCalldata : List Byte :=
  word32 0x20 ++ word32 1 ++ word32 42 ++ word32 0xdead

#guard headCheckDecodeOk
  (abiDecodeValuesExcept? [Ty.dynamicArray Ty.uint256]
    wellFormedTrailingGarbageCalldata)

/-! ### ABI-DECODE-TOTAL-HEAD-SIZE: upfront `slt(sub(dataEnd, headStart), N)`

solc's decoders OPEN with a total-head-size check before decoding ANY
component. 63 bytes of data for a `(uint256[], uint256)` head of 64
(`abi.encodePacked(uint256(31), uint248(1))`) revert EMPTY upfront; the model
previously followed offset 31 into an oversized length → Panic(0x41) — wrong
revert kind. Same for the nested dynamic-struct frame (`abi_decode_t_struct`'s
own `slt(sub(end, offset), headSize)`), and for the boundary decoder with an
eager `memory` param. -/

-- 63 bytes: head of `(uint256[], uint256)` needs 64.
def shortHeadPairData : List Byte :=
  word32 31 ++ (word32 1).drop 1

-- `abi.decode` path: EMPTY revert upfront, not Panic(0x41).
#guard headCheckIsEmptyRevert
  (abiDecodeValuesExcept? [Ty.dynamicArray Ty.uint256, Ty.uint256]
    shortHeadPairData)

-- Boundary path (eager `memory` params): same EMPTY revert.
#guard headCheckIsEmptyRevert
  (ABI.decodeArgsWith?
    [(false, Ty.dynamicArray Ty.uint256), (false, Ty.uint256)]
    shortHeadPairData)

-- Nested dynamic-struct frame: outer offset 32 → struct head needs 64, only 63
-- bytes remain → EMPTY at the struct-frame check (formerly the member offset 31
-- produced an oversized length → Panic(0x41)).
def shortHeadNestedTupleData : List Byte :=
  word32 32 ++ shortHeadPairData

#guard headCheckIsEmptyRevert
  (abiDecodeValuesExcept?
    [Ty.tuple [Ty.dynamicArray Ty.uint256, Ty.uint256]]
    shortHeadNestedTupleData)

-- Positive control: a well-formed `([42], 5)` encoding still decodes.
#guard headCheckDecodeOk
  (abiDecodeValuesExcept? [Ty.dynamicArray Ty.uint256, Ty.uint256]
    (word32 0x40 ++ word32 5 ++ word32 1 ++ word32 42))

end Source
end Solidity
end SolidCore

/- Build-time machine-check (same pattern as Phase5Demo): fails the library
   build if outgoing snapshots regress to the checkpoint-1 `default`
   placeholder. -/
#eval
  if SolidCore.Solidity.Source.snapshotWitnessMatches then
    (pure () : IO Unit)
  else
    throw (IO.userError
      "snapshotWitnessMatches failed: outgoing OpenWorld snapshot regressed")

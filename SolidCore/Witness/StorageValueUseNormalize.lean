import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
STORAGE-VALUE-USE-NORMALIZE (#192 endgame) — the NESTED / sibling cases the
shallow per-boundary `materializeStorageValueUseCore` rewrite missed, now
covered by the single position-aware pass
`SolidCore.Solidity.Source.Stmt.normalizeStorageValueUses` running once over
every emitted core body.

Five solc-0.8.35-accepted pipeline programs (all verified accepted with the
pinned binary) plus one CORE-level shape pin, each placing a bare state
`bytes`/`string` where its CONTENTS are consumed through a shape the old
rewrite could not reach:

1. NESTED TUPLE: `((a, x), y) = ((data, 7), 9)` — the inner tuple's
   components were never materialized (the old tuple arm only rewrote its
   own top-level components).
2. ARRAY LITERAL (core-level): a bare header read nested in `fixedArray`
   under `abiEncode` — the array-literal lowering had NO materialize call.
   The front-end currently over-rejects array literals of storage
   strings/bytes (fail-closed), so this position is pinned on the
   normalizer's output shape directly (see case 2 below).
3. STRUCT CONSTRUCTOR with a TERNARY field: `abi.encode(S(c ? b1 : b2, 5))`
   — the struct ctor lowers to a typed tuple, and the `bytes(<ternary>)`
   field cast passes the bare-header ternary through.
4. `bytes.concat` with a TERNARY argument selecting storage bytes.
5. `require(cond, Custom(storageBytes, 42))` — the `requireCustom` lowering
   arm never materialized its error args (asymmetric sibling of the fixed
   `Stmt.revert` arm).
6. Statement-position `revert(reason)` with a storage string — the
   `Stmt.revertCall` lowering arm never materialized the reason (asymmetric
   sibling of the fixed expression-position arm).

Pre-normalizer each of these fed a storage HEADER word (or a ternary over
header words) to a contents consumer → `asBytes?`/`abiEncodeValues?` = none
→ `Panic(0)`, diverging from solc+EVM, which implicitly copies storage to
memory at every one of these boundaries.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StorageValueUseNormalize

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def u256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]
private def u8 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional e]
private def byteAt (arr : String) (i : String) : Expr :=
  u256 (u8 (Expr.index (Expr.ident arr) (lit i)))
private def lenOf (arr : String) : Expr := Expr.member (Expr.ident arr) "length"
private def add (a b : Expr) : Expr := Expr.binary BinaryOp.add a b
private def mul (a b : Expr) : Expr := Expr.binary BinaryOp.mul a b
private def assignIdent (name : String) (rhs : Expr) : Stmt :=
  Stmt.expr (Expr.assign (Expr.ident name) AssignOp.assign rhs)
private def hexAssign (name value : String) : Stmt :=
  assignIdent name (Expr.literal (Literal.hexString value))
private def strAssign (name value : String) : Stmt :=
  assignIdent name (Expr.literal (Literal.string value))
private def retUint : List Parameter :=
  [{ name := none, ty := Ty.uint 256, location := none }]
private def mkRun (returns : List Parameter) (body : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := returns,
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }
private def mkUnit (decl : ContractDecl) : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract decl] }

/- 1. NESTED TUPLE — `bytes data; data = hex"1122";
      bytes memory a; uint x; uint y; ((a, x), y) = ((data, 7), 9);
      return a.length*1000 + x*100 + y*10 + uint256(uint8(a[0]))/16;`
   solc+EVM: a = hex"1122" (full copy), x = 7, y = 9 →
   2*1000 + 700 + 90 + (0x11 / 16 = 1) = 2791. -/
private def nestedTupleAssign : Stmt :=
  Stmt.expr
    (Expr.assign
      (Expr.tuple
        [ TupleItem.value (Expr.tuple
            [ TupleItem.value (Expr.ident "a")
            , TupleItem.value (Expr.ident "x") ])
        , TupleItem.value (Expr.ident "y") ])
      AssignOp.assign
      (Expr.tuple
        [ TupleItem.value (Expr.tuple
            [ TupleItem.value (Expr.ident "data")
            , TupleItem.value (lit "7") ])
        , TupleItem.value (lit "9") ]))

def nestedTupleContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C1",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "data", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "data" "1122"
          , Stmt.varDecl
              [{ name := some "a", ty := some Ty.bytes,
                 location := some DataLocation.memory }] none
          , Stmt.varDecl [{ name := some "x", ty := some (Ty.uint 256) }] none
          , Stmt.varDecl [{ name := some "y", ty := some (Ty.uint 256) }] none
          , nestedTupleAssign
          , Stmt.returnValues (some
              (add
                (add
                  (add (mul (lenOf "a") (lit "1000"))
                    (mul (Expr.ident "x") (lit "100")))
                  (mul (Expr.ident "y") (lit "10")))
                (Expr.binary BinaryOp.div (byteAt "a" "0") (lit "16")))) ] ] }

def nestedTupleAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit nestedTupleContract))

/- 2. ARRAY LITERAL — pinned at CORE level. The front-end currently
   OVER-REJECTS array literals of storage strings/bytes (`abi.encode([s1,
   s2])` fails to lower — fail-closed, a pre-existing coverage gap unrelated
   to materialization), so the array-literal VALUE-USE position cannot be
   reached through the pipeline today. The normalizer must still be correct
   there (the position exists in core and is one of the shapes the shallow
   materializer missed), so pin it directly: a bare header read nested in a
   `fixedArray` under `abiEncode` flips to the materializing `load`, while a
   `length` child (pointer use) keeps its header form — checked on the
   normalizer output shape below (`arrayLiteralNormalizeShape`). -/

/- 3. STRUCT CTOR w/ TERNARY — `bytes b1; bytes b2;
      struct S { bytes b; uint tag; }
      b1 = hex"aa"; b2 = hex"bbcc"; bool c = b1.length == 1;
      bytes memory e = abi.encode(S(c ? b1 : b2, 5));
      return e.length*1000 + uint256(uint8(e[95]))*100 + uint256(uint8(e[128]));`
   abi.encode(S mem) = [0x20][0x40][5][1][0xaa…] = 160 bytes; e[95] = 5,
   e[128] = 0xaa = 170 → 160*1000 + 500 + 170 = 160670. -/
def structCtorContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C3",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b1", ty := Ty.bytes }
      , ContractItem.stateVar { name := "b2", ty := Ty.bytes }
      , ContractItem.structDecl
          { name := "S",
            fields := [ { name := "b", ty := Ty.bytes }
                      , { name := "tag", ty := Ty.uint 256 } ] }
      , mkRun retUint
          [ hexAssign "b1" "aa"
          , hexAssign "b2" "bbcc"
          , Stmt.varDecl [{ name := some "c", ty := some Ty.bool }]
              (some (Expr.binary BinaryOp.eq (lenOf "b1") (lit "1")))
          , Stmt.varDecl
              [{ name := some "e", ty := some Ty.bytes,
                 location := some DataLocation.memory }]
              (some (Expr.call (Expr.member (Expr.ident "abi") "encode")
                [ Arg.positional
                    (Expr.call (Expr.typeName (Ty.user { segments := ["S"] }))
                      [ Arg.positional (Expr.ternary (Expr.ident "c")
                          (Expr.ident "b1") (Expr.ident "b2"))
                      , Arg.positional (lit "5") ]) ]))
          , Stmt.returnValues (some
              (add
                (add (mul (lenOf "e") (lit "1000"))
                  (mul (byteAt "e" "95") (lit "100")))
                (byteAt "e" "128"))) ] ] }

def structCtorAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit structCtorContract))

/- 4. bytes.concat w/ TERNARY — `bytes b1; bytes b2; b1 = hex"aa";
      b2 = hex"bbcc"; bool c = b1.length == 1;
      bytes memory e = bytes.concat(bytes(b1), c ? b1 : b2);
      return e.length*1000 + uint256(uint8(e[1]));`
   e = hex"aaaa" → 2*1000 + 0xaa = 2170. -/
def concatContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C4",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b1", ty := Ty.bytes }
      , ContractItem.stateVar { name := "b2", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "b1" "aa"
          , hexAssign "b2" "bbcc"
          , Stmt.varDecl [{ name := some "c", ty := some Ty.bool }]
              (some (Expr.binary BinaryOp.eq (lenOf "b1") (lit "1")))
          , Stmt.varDecl
              [{ name := some "e", ty := some Ty.bytes,
                 location := some DataLocation.memory }]
              (some (Expr.call (Expr.member (Expr.ident "bytes") "concat")
                [ Arg.positional (Expr.call (Expr.typeName Ty.bytes)
                    [Arg.positional (Expr.ident "b1")])
                , Arg.positional (Expr.ternary (Expr.ident "c")
                    (Expr.ident "b1") (Expr.ident "b2")) ]))
          , Stmt.returnValues (some
              (add (mul (lenOf "e") (lit "1000")) (byteAt "e" "1"))) ] ] }

def concatAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit concatContract))

/- 5. requireCustom args — `bytes payloadData; error Custom(bytes, uint256);
      payloadData = hex"c0de";
      require(payloadData.length == 3, Custom(payloadData, 42));`
   The condition is FALSE (length is 2), so solc+EVM reverts
   `Custom(hex"c0de", 42)` with the storage bytes CONTENTS. -/
def requireCustomContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C5",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "payloadData", ty := Ty.bytes }
      , ContractItem.errorDecl
          { name := "Custom",
            params := [ { ty := Ty.bytes }, { ty := Ty.uint 256 } ] }
      , mkRun []
          [ hexAssign "payloadData" "c0de"
          , Stmt.expr
              (Expr.call (Expr.ident "require")
                [ Arg.positional (Expr.binary BinaryOp.eq
                    (lenOf "payloadData") (lit "3"))
                , Arg.positional (Expr.call (Expr.ident "Custom")
                    [ Arg.positional (Expr.ident "payloadData")
                    , Arg.positional (lit "42") ]) ]) ] ] }

def requireCustomAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit requireCustomContract))

/- 6. statement-position `revert(reason)` w/ storage string —
      `string reason; reason = "nope"; revert(reason);`
   solc+EVM reverts `Error("nope")`. -/
def revertReasonContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C6",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "reason", ty := Ty.string }
      , mkRun []
          [ strAssign "reason" "nope"
          , Stmt.revertCall
              (Expr.call (Expr.ident "revert")
                [Arg.positional (Expr.ident "reason")]) ] ] }

def revertReasonAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit revertReasonContract))

/- 2'. ARRAY LITERAL — PROMOTED to SOURCE level (ITEM-1). The front-end now
   types inline array literals of storage `bytes`/`string` env-aware
   (`Expr.abiArrayLiteralWithEnvFuel?` decline-fallback), so the shape the
   core-level pin (case 2) covers is reachable through the pipeline:
   `bytes b1; bytes b2; b1 = hex"aa"; b2 = hex"bbcc";
    bytes memory e = abi.encode([b1, b2]);
    return e.length*1000000 + uint(uint8(e[128]))*1000 + uint(uint8(e[192]));`
   solc+EVM (pinned 0.8.35, Forge lane `storage-array-literal`):
   enc(bytes[2]) = [0x20][0x40][0x80][1][aa..][2][bbcc..] = 224 bytes,
   e[128] = 0xaa = 170, e[192] = 0xbb = 187 → 224170187. -/
private def encProbeReturn (e : String) : Stmt :=
  Stmt.returnValues (some
    (add
      (add (mul (lenOf e) (lit "1000000"))
        (mul (byteAt e "128") (lit "1000")))
      (byteAt e "192")))

def arrayLiteralSourceContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C2S",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b1", ty := Ty.bytes }
      , ContractItem.stateVar { name := "b2", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "b1" "aa"
          , hexAssign "b2" "bbcc"
          , Stmt.varDecl
              [{ name := some "e", ty := some Ty.bytes,
                 location := some DataLocation.memory }]
              (some (Expr.call (Expr.member (Expr.ident "abi") "encode")
                [ Arg.positional
                    (Expr.array [Expr.ident "b1", Expr.ident "b2"]) ]))
          , encProbeReturn "e" ] ] }

def arrayLiteralSourceAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      (mkUnit arrayLiteralSourceContract))

/- 7'. STORAGE-POINTER LOCALS in an array literal — PROMOTED to SOURCE level
   (ITEM-1): `bytes storage p1 = b1; bytes storage p2 = b2;
   abi.encode([p1, p2])` — the runtime twin (case 7) pinned the nested
   `Value.storageRef` materialization on hand-built core; the front-end now
   accepts the source form. Same encoding as 2' → 224170187 (Forge lane
   `storage-array-literal`, test `testEncPointers`). -/
def pointerArrayLiteralSourceContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C7S",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b1", ty := Ty.bytes }
      , ContractItem.stateVar { name := "b2", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "b1" "aa"
          , hexAssign "b2" "bbcc"
          , Stmt.varDecl
              [{ name := some "p1", ty := some Ty.bytes,
                 location := some DataLocation.storage }]
              (some (Expr.ident "b1"))
          , Stmt.varDecl
              [{ name := some "p2", ty := some Ty.bytes,
                 location := some DataLocation.storage }]
              (some (Expr.ident "b2"))
          , Stmt.varDecl
              [{ name := some "e", ty := some Ty.bytes,
                 location := some DataLocation.memory }]
              (some (Expr.call (Expr.member (Expr.ident "abi") "encode")
                [ Arg.positional
                    (Expr.array [Expr.ident "p1", Expr.ident "p2"]) ]))
          , encProbeReturn "e" ] ] }

def pointerArrayLiteralSourceAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      (mkUnit pointerArrayLiteralSourceContract))

end StorageValueUseNormalize
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace StorageValueUseNormalize

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
open SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- 1. Nested tuple: 2791 (pre-normalizer: Panic(0) at the inner-tuple copy).
def nestedTuple_is_2791 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 nestedTupleContract "run"
    State.empty [] 2791

-- 2. Array literal, CORE-level shape pin (see the case-2 comment in the
-- import section): a bare header read nested in `fixedArray` under
-- `abiEncode` materializes; the `length` child keeps its header form; a
-- nested ternary's branches materialize while its condition does not.
private def alInput : Source.Expr :=
  Source.Expr.abiEncode [Source.Ty.bytesCalldata]
    [ Source.Expr.fixedArray
        [ Source.Expr.storageIdent "b1"
        , Source.Expr.length (Source.Expr.storageIdent "b2")
        , Source.Expr.binary Source.BinaryOp.sub
            (Source.Expr.storage "b2") (Source.Expr.word 1)
        , Source.Expr.ternary (Source.Expr.storageIdent "flag")
            (Source.Expr.storageIdent "b1") (Source.Expr.storageIdent "b2") ] ]

private def alExpected : Source.Expr :=
  Source.Expr.abiEncode [Source.Ty.bytesCalldata]
    [ Source.Expr.fixedArray
        [ -- bare reference nested in the array literal: MATERIALIZED
          Source.Expr.storagePath "b1" []
        , -- `.length` child is a pointer use: the reference survives
          Source.Expr.length (Source.Expr.storageIdent "b2")
        , -- deliberate header-word arithmetic (the synthesized
          -- push-last-index shape): NEVER rewritten
          Source.Expr.binary Source.BinaryOp.sub
            (Source.Expr.storage "b2") (Source.Expr.word 1)
        , -- ternary: branches materialize, the boolean condition does not
          Source.Expr.ternary (Source.Expr.storageIdent "flag")
            (Source.Expr.storagePath "b1" []) (Source.Expr.storagePath "b2" []) ] ]

def arrayLiteralNormalizeShape : Bool :=
  reprStr
      (Source.Expr.normalizeStorageValueUses
        Source.StoragePosition.pointerUse alInput) ==
    reprStr alExpected

-- 3. Struct ctor w/ ternary: 160670 (pre-normalizer: Panic(0)).
def structCtor_is_160670 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 structCtorContract "run"
    State.empty [] 160670

-- 4. bytes.concat w/ ternary: 2170 (pre-normalizer: Panic(0)).
def concat_is_2170 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 concatContract "run"
    State.empty [] 2170

-- 5. requireCustom args carry the storage bytes CONTENTS.
def requireCustom_reverts_contents : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64 requireCustomContract
      (CallTarget.name "run") State.empty []
  match result with
  | CallResult.reverted _
      (RevertData.custom "Custom" [Value.bytes bs, Value.word code]) =>
      Except.ok (bs == [0xc0, 0xde] && code == 42)
  | _ => Except.ok false

-- 6. Statement-position `revert(reason)` reverts `Error("nope")`.
private def nopeBytes : List Byte := [110, 111, 112, 101]

def revertReason_reverts_error_nope : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64 revertReasonContract
      (CallTarget.name "run") State.empty []
  match result with
  | CallResult.reverted _ (RevertData.raw bytes) =>
      Except.ok
        (bytes.take 4 == [8, 195, 121, 160]          -- Error(string) selector
          && bytes.length == 100                     -- 4 + 3*32
          && (bytes.drop 68).take 4 == nopeBytes)
  | CallResult.reverted _ (RevertData.error reason) =>
      Except.ok (reason == "nope")
  | _ => Except.ok false

#guard nestedTupleAccepted
#guard structCtorAccepted
#guard concatAccepted
#guard requireCustomAccepted
#guard revertReasonAccepted

#guard isOkTrue nestedTuple_is_2791
#guard arrayLiteralNormalizeShape
#guard isOkTrue structCtor_is_160670
#guard isOkTrue concat_is_2170
#guard isOkTrue requireCustom_reverts_contents
#guard isOkTrue revertReason_reverts_error_nope

/- 7. RUNTIME deep value-use materialization — a storage-pointer LOCAL nested
   inside an aggregate VALUE at an encode boundary. solc 0.8.35 accepts
   `bytes storage p1 = b1; bytes storage p2 = b2; abi.encode([p1, p2])`
   (verified with the pinned binary); the front-end currently over-rejects
   the array-literal shape, so pin the RUNTIME twin directly on a hand-built
   CORE contract: `Value.storageRef`s nested in a `Value.fixedArray` under
   `abiEncode` load their CONTENTS (previously they survived to
   `abiEncodeValues?` unloaded → Panic(0)). Encoding of `bytes[2]` =
   [0x20][0x40][0x80][1][aa…][1][aa…] = 224 bytes. -/
private def coreNestedRefFn : Source.FunctionDef :=
  { name := "encNested", selector? := none
    params := [], returns := [{ name := "out", ty := Source.Ty.bytesCalldata }]
    body := Source.Stmt.block
      [ Source.Stmt.assign (Source.LValue.storage "b1")
          (Source.Expr.byteArray [0xaa])
      , Source.Stmt.storageAlias "p1" "b1"
      , Source.Stmt.returnValues
          [ Source.Expr.abiEncode
              [Source.Ty.fixedArray 2 Source.Ty.bytesCalldata]
              [ Source.Expr.fixedArray
                  [Source.Expr.var "p1", Source.Expr.var "p1"] ] ] ] }

private def coreNestedRefContract : Source.Contract :=
  { storageFields :=
      [ { name := "b1", slot := 0,
          layout? := some Source.StorageLayout.bytes } ]
    functions := [coreNestedRefFn] }

def coreNestedRefEncodes : Bool :=
  match Source.Contract.call? 1000 coreNestedRefContract
      (Source.CallTarget.name "encNested") Source.State.empty [] with
  | some (Source.CallResult.returned _ [Source.Value.bytes bs]) =>
      bs.length == 224 &&
        List.getLast? (List.take 32 bs) == some 0x20 &&
        List.getLast? (List.take 32 (List.drop 96 bs)) == some 1 &&
        List.take 1 (List.drop 128 bs) == [0xaa] &&
        List.take 1 (List.drop 192 bs) == [0xaa]
  | _ => false

#guard coreNestedRefEncodes

-- 2'/7' (ITEM-1 promotion): the SOURCE forms of the two core-pinned shapes
-- now lower through the pipeline and produce the Forge-validated word
-- (224170187 on pinned solc 0.8.35 + real EVM, lane `storage-array-literal`).
def arrayLiteralSource_is_224170187 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 arrayLiteralSourceContract "run"
    State.empty [] 224170187

def pointerArrayLiteralSource_is_224170187 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 pointerArrayLiteralSourceContract
    "run" State.empty [] 224170187

#guard arrayLiteralSourceAccepted
#guard pointerArrayLiteralSourceAccepted
#guard isOkTrue arrayLiteralSource_is_224170187
#guard isOkTrue pointerArrayLiteralSource_is_224170187

end StorageValueUseNormalize
end Witness
end Solidity
end SolidCore

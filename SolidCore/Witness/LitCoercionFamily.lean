import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
LIT-COERCION FAMILY (#141-#145) — literal -> fixed `bytesN` target coercion.

A string/hex/bytes LITERAL flowing into a declared fixed `bytesN` target through
a target-BLIND lowering path (emit/revert/require args, `.push`, mapping key,
`encodeWithSelector` selector, external function-pointer call args) must be
coerced by solc to the fixed target — ONE left-aligned 32-byte word (the <= n
meaningful bytes at the top, zero-padded). These witnesses drive the imported
source through the source semantics and pin the corrected observable bytes; real
-EVM Forge ground truth lives in `tests/forge-harness/lit-coercion-family`.

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LitCoercionFamily

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/wt-coercion/tests/forge-harness/lit-coercion-family/src/LitCoercionFamily.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "LitCoercionFamily"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "EvData",
    params := [{ name := some "x", ty := Ty.bytesN 2, indexed := false }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "EvIdx",
    params := [{ name := some "x", ty := Ty.bytesN 2, indexed := true }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "EvDyn",
    params := [{ name := some "x", ty := Ty.bytes, indexed := false }],
    anonymous := false }), (ContractItem.errorDecl
  { name := "Bad",
    params := [{ name := some "x", ty := Ty.bytesN 2, location := none }] }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.bytesN 2) (none),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.bytesN 4) (Ty.uint 256),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitData",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EvData") [Arg.positional (Expr.literal (Literal.hexString "1234"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitIdx",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EvIdx") [Arg.positional (Expr.literal (Literal.hexString "1234"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "doRevert",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.ident "Bad") [Arg.positional (Expr.literal (Literal.hexString "1234"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "doRequire",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.literal (Literal.bool false)), Arg.positional (Expr.call (Expr.ident "Bad") [Arg.positional (Expr.literal (Literal.hexString "1234"))])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushLit",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.literal (Literal.hexString "1234"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "setMap",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.literal (Literal.string "abcd"))) AssignOp.assign (Expr.literal (Literal.number "7")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "selData",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector") [Arg.positional (Expr.literal (Literal.number "0x12345678")), Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "7"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitDyn",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EvDyn") [Arg.positional (Expr.literal (Literal.hexString "1234"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitVar",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.bytesN 2, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EvData") [Arg.positional (Expr.ident "v")])]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "LitPtrTarget"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "z", ty := Ty.bytesN 4, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "z"))]) })] }

def importedContractDecl2 : ContractDecl :=
{ kind := ContractKind.contract
  name := "LitPtrCaller"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "callPtr",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "t", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "fn", ty := Ty.functionWithLocations [Ty.bytesN 4] [none] [Ty.bytesN 4] [none] StateMutability.nonpayable Visibility.external_, location := none }] (some (Expr.member (Expr.call (Expr.typeName (Ty.user ({ segments := ["LitPtrTarget"] }))) [Arg.positional (Expr.ident "t")]) "g")), Stmt.returnValues (some (Expr.call (Expr.ident "fn") [Arg.positional (Expr.literal (Literal.string "abcd"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1, importedContractDecl2]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1, SourceItem.contract importedContractDecl2] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end LitCoercionFamily
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace LitCoercionFamily

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

def leftWordBytes : List Byte :=
  wordToBytesBE wordBytes 0x1234000000000000000000000000000000000000000000000000000000000000
def leftWord : Word :=
  0x1234000000000000000000000000000000000000000000000000000000000000
def badSelector : List Byte := [0xfd, 0xa2, 0x8e, 0xa8]

abbrev Src := SolidCore.Solidity.SolcAstImport.LitCoercionFamily.importedSourceUnit
abbrev Fam := SolidCore.Solidity.SolcAstImport.LitCoercionFamily.importedContract

-- The whole family source unit type-checks (accepted).
def familyAccepted : Bool := SolidCore.Solidity.SolcAstImport.LitCoercionFamily.importedContractAccepted

-- #141 emit: hex literal -> bytes2 event field, non-indexed data word.
def emitDataLeftAlignedWord : Except TypeError Bool := do
  let result ← CheckedInput.ownCall 32 Fam (CallTarget.name "emitData") State.empty []
  match result with
  | CallResult.returned state [] =>
      match state.events with
      | [ev] =>
          Except.ok
            (ev.name == "EvData" &&
              ev.topics == [Keccak.digestWord "EvData(bytes2)"] &&
              ev.dataBytes == leftWordBytes)
      | _ => Except.ok false
  | _ => Except.ok false

-- #141 emit: hex literal -> bytes2 INDEXED event field, topic word (unhashed).
def emitIndexedTopicLeftAlignedWord : Except TypeError Bool := do
  let result ← CheckedInput.ownCall 32 Fam (CallTarget.name "emitIdx") State.empty []
  match result with
  | CallResult.returned state [] =>
      match state.events with
      | [ev] =>
          Except.ok
            (ev.name == "EvIdx" &&
              ev.topics == [Keccak.digestWord "EvIdx(bytes2)", leftWord] &&
              ev.dataBytes == [])
      | _ => Except.ok false
  | _ => Except.ok false

-- #141 revert: encoded custom-error data is selector + one left-aligned word.
def revertCustomErrorOneWord : Except TypeError Bool := do
  let program ← CheckedInput.program Src
  let c ← CheckedProgram.contract program "LitCoercionFamily"
  let cd ← CheckedContract.functionCalldata c "doRevert" []
  let r ← CheckedContract.callCalldata 64 c State.empty cd
  Except.ok (!r.success && r.output == (badSelector ++ leftWordBytes))

-- #141 require with custom error: same encoded data.
def requireCustomErrorOneWord : Except TypeError Bool := do
  let program ← CheckedInput.program Src
  let c ← CheckedProgram.contract program "LitCoercionFamily"
  let cd ← CheckedContract.functionCalldata c "doRequire" []
  let r ← CheckedContract.callCalldata 64 c State.empty cd
  Except.ok (!r.success && r.output == (badSelector ++ leftWordBytes))

-- #142 push: pushed bytes2 element reads back as the left-aligned word value.
def pushLiteralElementLeftAlignedWord : Except TypeError Bool := do
  let r1 ← CheckedInput.ownCall 32 Fam (CallTarget.name "pushLit") State.empty []
  match r1 with
  | CallResult.returned st _ =>
      let r2 ← CheckedInput.ownCall 32 Fam (CallTarget.name "arr") st [Value.word 0]
      match r2 with
      -- R3: the bytes2 element now carries its width; compare the raw word.
      | CallResult.returned _ [v] =>
          Except.ok (v.asWord? == some 0x1234)
      | _ => Except.ok false
  | _ => Except.ok false

-- #145 mapping key: string-literal key stores and reads at the same slot.
def mappingBytesNKeyStoresAndReads : Except TypeError Bool := do
  let r1 ← CheckedInput.ownCall 32 Fam (CallTarget.name "setMap") State.empty []
  match r1 with
  | CallResult.returned st _ =>
      let r2 ← CheckedInput.ownCall 32 Fam (CallTarget.name "m") st [Value.word 0x61626364]
      match r2 with
      | CallResult.returned _ [Value.word v] => Except.ok (wordEq v 7)
      | _ => Except.ok false
  | _ => Except.ok false

-- #143 encodeWithSelector: bare 4-byte hex NUMBER literal selector accepted.
def encodeWithSelectorBareHexLiteral : Except TypeError Bool := do
  let r ← CheckedInput.ownCall 32 Fam (CallTarget.name "selData") State.empty []
  match r with
  | CallResult.returned _ [Value.bytes b] =>
      Except.ok (b == (([0x12, 0x34, 0x56, 0x78] : List Byte) ++ wordToBytesBE wordBytes 7))
  | _ => Except.ok false

-- #144 external function-pointer value call: the literal arg is a left-aligned
-- word inside the call's calldata (nonpayable pointer -> CALL).
def externalFunctionPointerArgLeftAlignedWord : Except TypeError Bool := do
  let argWord : List Byte := ([0x61, 0x62, 0x63, 0x64] : List Byte) ++ List.replicate 28 0
  let calldata : List Byte := ([0xe2, 0x2d, 0x9c, 0xb4] : List Byte) ++ argWord
  let row : LowLevelCallResult :=
    { kind := LowLevelCallKind.call, target := 0xc0ffee, calldata := calldata,
       value := 0, gas? := none, success := true, output := argWord }
  let program ← CheckedInput.program Src
  let contract ← CheckedProgram.contract program "LitPtrCaller"
  let result ← CheckedContract.callFunctionWithContextUnderResponder 64
    (responderOfResults [row] []) contract "callPtr" contract.core.context State.empty
    [Value.word 0xc0ffee]
  match result with
  | CallResult.returned _ [retValue] =>
      match (CallResult.resultState result).externalInteractions with
      | [ExternalInteraction.lowLevelCall call] =>
          Except.ok
            (retValue.asWord? == some 0x61626364 &&
              LowLevelCallResult.matches call LowLevelCallKind.call 0xc0ffee calldata 0 none &&
              call.success)
      | _ => Except.ok false
  | _ => Except.ok false

-- CONTROL: a literal into a DYNAMIC bytes event field stays dynamic
-- (offset/length/data), NOT the single fixed word.
def controlDynamicBytesFieldStaysDynamic : Except TypeError Bool := do
  let program ← CheckedInput.program Src
  let c ← CheckedProgram.contract program "LitCoercionFamily"
  let cd ← CheckedContract.functionCalldata c "emitDyn" []
  let r ← CheckedContract.callCalldata 64 c State.empty cd
  match r.state.events with
  | [ev] =>
      Except.ok
        (ev.dataBytes.length == 96 &&
          ev.dataBytes ==
            (wordToBytesBE wordBytes 0x20 ++ wordToBytesBE wordBytes 2 ++
              (([0x12, 0x34] : List Byte) ++ List.replicate 30 0)))
  | _ => Except.ok false

-- CONTROL: a NON-literal bytes2 variable arg is byte-identical to the literal.
def controlNonLiteralVariableArgUnchanged : Except TypeError Bool := do
  let result ← CheckedInput.ownCall 32 Fam (CallTarget.name "emitVar") State.empty [Value.word 0x1234]
  match result with
  | CallResult.returned state [] =>
      match state.events with
      | [ev] => Except.ok (ev.dataBytes == leftWordBytes)
      | _ => Except.ok false
  | _ => Except.ok false

-- #143 NEGATIVE acceptance: a 2-byte hex literal selector (`0x1234`, compatible
-- type `bytes2`, NOT implicitly `bytes4`) and any DECIMAL literal selector are
-- rejected — matching solc, which rejects both. Build a minimal contract whose
-- only function returns `abi.encodeWithSelector(<sel>, uint256(7))`.
private def selUnit (sel : Literal) : SourceUnit :=
  { items :=
      [SourceItem.pragma "solidity" "^0.8.35",
       SourceItem.contract
        { kind := ContractKind.contract, name := "SelReject", abstract := false,
           bases := [],
           items :=
            [ContractItem.function
              { kind := FunctionKind.function, name := some "f",
                 visibility := some Visibility.external_,
                 mutability := StateMutability.pure, params := [],
                 returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
                 virtual := false, override? := none, modifiers := [],
                 body := some
                  (Stmt.block
                    [Stmt.returnValues
                      (some
                        (Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector")
                          [Arg.positional (Expr.literal sel),
                           Arg.positional
                            (Expr.call (Expr.typeName (Ty.uint 256))
                              [Arg.positional (Expr.literal (Literal.number "7"))])]))]) }] }] }

def twoByteHexSelectorRejected : Bool :=
  !(TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (selUnit (Literal.number "0x1234"))))

def decimalSelectorRejected : Bool :=
  !(TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (selUnit (Literal.number "305419896"))))

-- The exact-width 4-byte hex selector, by contrast, IS accepted.
def fourByteHexSelectorAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit (selUnit (Literal.number "0x12345678")))

#guard familyAccepted
#guard isOkTrue emitDataLeftAlignedWord
#guard isOkTrue emitIndexedTopicLeftAlignedWord
#guard isOkTrue revertCustomErrorOneWord
#guard isOkTrue requireCustomErrorOneWord
#guard isOkTrue pushLiteralElementLeftAlignedWord
#guard isOkTrue mappingBytesNKeyStoresAndReads
#guard isOkTrue encodeWithSelectorBareHexLiteral
#guard isOkTrue externalFunctionPointerArgLeftAlignedWord
#guard isOkTrue controlDynamicBytesFieldStaysDynamic
#guard isOkTrue controlNonLiteralVariableArgUnchanged
#guard twoByteHexSelectorRejected
#guard decimalSelectorRejected
#guard fourByteHexSelectorAccepted

end LitCoercionFamily
end Witness
end Solidity
end SolidCore

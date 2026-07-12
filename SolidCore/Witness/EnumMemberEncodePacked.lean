import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ENUM-MEMBER-ENCODEPACKED (#178) — an enum MEMBER-ACCESS literal (`E.C`) passed
to `abi.encodePacked` formerly packed to a full 32-byte word instead of its
1-byte (`uint8`) underlying width.

Root cause: `Expr.resolveEnumsFuel` (`SolidCore/Solidity/Interface.lean`)
rewrote `E.C` into a BARE `Expr.literal (Literal.number "2")`, discarding the
enum-ness. Downstream `Ty.packedTopWidth` (via `Expr.abiTy?`) therefore never
saw an enum type and packed at the full-word default. The `E(x)` CONVERSION form
was already correct because it produced `Expr.enumFromUInt`, which `Expr.abiTy?`
maps to `Ty.uint 8` → packed width 1.

The fix wraps the resolved ordinal of a member literal in `Expr.enumFromUInt`
(mirroring the `E(x)` form) so the enum width is retained everywhere `E.C`
appears. `Expr.numberLiteralRat?` now looks through `enumFromUInt`, so constant
contexts (e.g. the `uint8 constant X = uint8(E.C)` initializer below) still fold
and accept.

Ground truth (pinned solc 0.8.35 legacy + real EVM via Forge,
`tests/forge-harness/enum-member-encodepacked`):
  enum E { A, B, C, D };
  abi.encodePacked(E.C)                    == 0x02       (1 byte)
  abi.encodePacked(uint8(1), E.C, uint8(9)) == 0x010209   (3 bytes)
  uint8 constant X = uint8(E.C);  X        == 2           (const folds/accepts)
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EnumMemberEncodePacked

def importedSourceName : String := "tests/forge-harness/enum-member-encodepacked/src/EnumMemberEncodePacked.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "EnumMemberEncodePacked"
  abstract := false
  bases := []
  items := [(ContractItem.enumDecl
  { name := "E",
    cases := ["A", "B", "C", "D"] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "packMember",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.member (Expr.typeName (Ty.user ({ segments := ["E"] }))) "C")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "packMixed",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "1"))]), Arg.positional (Expr.member (Expr.typeName (Ty.user ({ segments := ["E"] }))) "C"), Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "9"))])]))]) }), (ContractItem.stateVar
  { name := "X",
    ty := Ty.uint 8,
    visibility := some Visibility.internal_,
    mutability := VarMutability.constant,
    override? := none,
    init := some (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.member (Expr.typeName (Ty.user ({ segments := ["E"] }))) "C")]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "constFold",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "X"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EnumMemberEncodePacked
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EnumMemberEncodePacked

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.EnumMemberEncodePacked.importedContract

-- The imported contract type-checks (accepted). Acceptance held BEFORE the fix
-- too — only the packed width diverged — but the `uint8(E.C)` const initializer
-- now folds through the `enumFromUInt` wrapper, so acceptance is preserved.
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EnumMemberEncodePacked.importedContractAccepted

private def callBytesMatches (fn : Name) (expected : List Byte) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 256 Fam (CallTarget.name fn) State.empty []
  match result with
  | CallResult.returned _ [Value.bytes actual] => Except.ok (actual == expected)
  | _ => Except.ok false

private def callWordMatches (fn : Name) (expected : Word) :
    Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam fn State.empty [] expected

-- #178: enum member literal packs to its 1-byte underlying width.
--   abi.encodePacked(E.C) == 0x02.
def packMember_is_02 : Except TypeError Bool :=
  callBytesMatches "packMember" [0x02]

-- Mixed: abi.encodePacked(uint8(1), E.C, uint8(9)) == 0x010209.
def packMixed_is_010209 : Except TypeError Bool :=
  callBytesMatches "packMixed" [0x01, 0x02, 0x09]

-- Constant-context regression guard: `uint8 constant X = uint8(E.C)` folds and
-- the value is 2 (the `enumFromUInt` wrapper stays foldable).
def constFold_is_2 : Except TypeError Bool :=
  callWordMatches "constFold" 2

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue packMember_is_02
#guard isOkTrue packMixed_is_010209
#guard isOkTrue constFold_is_2

end EnumMemberEncodePacked
end Witness
end Solidity
end SolidCore

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
EXP-NARROW-BASE-WIDE-EXPONENT (#164) — `**` is NOT a symmetric binary op.

Per solc (`IntegerType::binaryOperatorResult` / `Token::Exp`, `Types.cpp`), the
RESULT type of `base ** e` is the BASE (left-operand) type ONLY — "ignoring the
(larger) type of the second operand" (the compile-time warning). The exponent
keeps its own type and is NOT folded into a common-type computation, so the
checked exponentiation and its overflow Panic 0x11 run at the BASE width even
when the exponent is wider.

solidity-lean formerly treated `**` symmetrically (`Expr.binaryToCoreWithEnvTyped?`
computed `commonImplicit? uint8 uint16 = uint16` and ran the checked-exp at that
width), so `uint8 base ** uint16 e` with `2 ** 8 = 256` fit the wider uint16 and
the uint8 Panic 0x11 was silently lost. The fix special-cases `BinaryOp.exp`:
the base (and the returned result type) lower at the base type; the exponent
lowers at its own type.

Real-EVM Forge ground truth: `tests/forge-harness/exp-narrow-base-wide-exp`.
`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ExpNarrowBaseWideExpWitness

def importedSourceName : String :=
  "tests/forge-harness/exp-narrow-base-wide-exp/src/ExpNarrowBaseWideExp.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "ExpNarrowBaseWideExpTarget"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "base", ty := Ty.uint 8, location := none }, { name := some "e", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.uint 16, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.exp (Expr.ident "base") (Expr.ident "e")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "base", ty := Ty.uint 8, location := none }, { name := some "e", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.uint 16, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 16)) [Arg.positional (Expr.binary BinaryOp.exp (Expr.ident "base") (Expr.ident "e"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mirror",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "base", ty := Ty.uint 16, location := none }, { name := some "e", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 16, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.exp (Expr.ident "base") (Expr.ident "e")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "wideBase",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "base", ty := Ty.uint 256, location := none }, { name := some "e", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.exp (Expr.ident "base") (Expr.ident "e")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sgn",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "base", ty := Ty.int 8, location := none }, { name := some "e", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.int 16, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.exp (Expr.ident "base") (Expr.ident "e")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ExpNarrowBaseWideExpWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace ExpNarrowBaseWideExp

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.ExpNarrowBaseWideExpWitness.importedContract

-- The source unit type-checks (accepted).
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.ExpNarrowBaseWideExpWitness.importedContractAccepted

-- The repro: uint8 base ** uint16 exponent, returned as uint16.
-- g(2,7) = 128 fits uint8, no panic.
def g_2_7_is_128 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "g" State.empty
    [Value.word 2, Value.word 7] 128

-- g(2,8) = 256 overflows uint8 -> Panic 0x11 (formerly silently produced 256).
def g_2_8_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "g" State.empty
    [Value.word 2, Value.word 8] 17

-- g(2,10) = 1024 overflows uint8 -> Panic 0x11.
def g_2_10_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "g" State.empty
    [Value.word 2, Value.word 10] 17

-- h(2,8): explicit uint16 cast around the exp is still base-width checked.
def h_2_8_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "h" State.empty
    [Value.word 2, Value.word 8] 17

-- Mirror: base WIDER than exponent (uint16 ** uint8) -> correct value, no panic.
def mirror_2_8_is_256 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "mirror" State.empty
    [Value.word 2, Value.word 8] 256

-- Wide base, narrow exponent: full 256-bit value, no panic (2^200).
def wideBase_2_200 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "wideBase" State.empty
    [Value.word 2, Value.word 200]
    1606938044258990275541962092341162602522202993782792835301376

-- Signed narrow base, wider exponent: result type is the base type (int8).
-- (-2)^7 = -128 = type(int8).min, fits.
def sgn_neg2_7_is_min : Except TypeError Bool :=
  Examples.checkedOwnCallIntMatches 256 Fam "sgn" State.empty
    [Value.int (SolidCore.Solidity.Shared.signedToWord (-2)), Value.word 7]
    (SolidCore.Solidity.Shared.signedToWord (-128))

-- 2^7 = 128 > type(int8).max (127) -> Panic 0x11 at the base (int8) width.
def sgn_2_7_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "sgn" State.empty
    [Value.int (SolidCore.Solidity.Shared.signedToWord 2), Value.word 7] 17

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue g_2_7_is_128
#guard isOkTrue g_2_8_panics
#guard isOkTrue g_2_10_panics
#guard isOkTrue h_2_8_panics
#guard isOkTrue mirror_2_8_is_256
#guard isOkTrue wideBase_2_200
#guard isOkTrue sgn_neg2_7_is_min
#guard isOkTrue sgn_2_7_panics

end ExpNarrowBaseWideExp
end Witness
end Solidity
end SolidCore

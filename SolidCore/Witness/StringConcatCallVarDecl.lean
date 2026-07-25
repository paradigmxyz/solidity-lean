import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
STRINGCONCAT-CALL-VARDECL repro (candidate divergence).

  contract T {
    uint256 tr;                                   // slot 0
    function sfn() internal returns (string memory) { tr = tr*10+4; return "b"; }
    function run() public returns (uint256) {
      string memory s = string.concat("a", sfn());
      return bytes(s).length + tr;
    }
  }

sfn() runs (tr := 4, returns "b"); s = "ab" (length 2); run returns 2 + 4 = 6,
storage slot 0 == 4. solc+EVM: success, w:6, sto 0:4.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StringConcatCallVarDecl

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def scat (a : List Arg) : Expr :=
  Expr.call (Expr.member (Expr.ident "string") "concat") a

private def trVar : ContractItem := ContractItem.stateVar
  { name := "tr", ty := Ty.uint 256, visibility := some Visibility.internal_ }

-- tr = tr*10 + 4 ; return "b"
private def sfnFn : ContractItem := ContractItem.function
  { name := some "sfn", visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.string, location := some DataLocation.memory }],
    body := some (Stmt.block [
      Stmt.expr (Expr.assign (Expr.ident "tr") AssignOp.assign
        (Expr.binary BinaryOp.add
          (Expr.binary BinaryOp.mul (Expr.ident "tr") (lit "10")) (lit "4"))),
      Stmt.returnValues (some (Expr.literal (Literal.string "b"))) ]) }

private def runFn : ContractItem := ContractItem.function
  { name := some "run", visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [
      Stmt.varDecl [{ name := some "s", ty := some Ty.string, location := some DataLocation.memory }]
        (some (scat [Arg.positional (Expr.literal (Literal.string "a")),
                     Arg.positional (Expr.call (Expr.ident "sfn") [])])),
      Stmt.returnValues (some
        (Expr.binary BinaryOp.add
          (Expr.member
            (Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.ident "s")]) "length")
          (Expr.ident "tr"))) ]) }

-- Variant: concat in RETURN position (no varDecl), side-effecting call second.
private def runRetFn : ContractItem := ContractItem.function
  { name := some "runRet", visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [
      Stmt.returnValues (some
        (Expr.binary BinaryOp.add
          (Expr.member
            (Expr.call (Expr.typeName Ty.bytes)
              [Arg.positional (scat [Arg.positional (Expr.literal (Literal.string "a")),
                                     Arg.positional (Expr.call (Expr.ident "sfn") [])])]) "length")
          (Expr.ident "tr"))) ]) }

-- Variant: varDecl, side-effecting call in FIRST position.
private def runFirstFn : ContractItem := ContractItem.function
  { name := some "runFirst", visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [
      Stmt.varDecl [{ name := some "s", ty := some Ty.string, location := some DataLocation.memory }]
        (some (scat [Arg.positional (Expr.call (Expr.ident "sfn") []),
                     Arg.positional (Expr.literal (Literal.string "a"))])),
      Stmt.returnValues (some
        (Expr.binary BinaryOp.add
          (Expr.member
            (Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.ident "s")]) "length")
          (Expr.ident "tr"))) ]) }

-- Variant: MANUALLY hoisted — concat of a plain string local in a varDecl init.
private def runManualFn : ContractItem := ContractItem.function
  { name := some "runManual", visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [
      Stmt.varDecl [{ name := some "h0", ty := some Ty.string, location := some DataLocation.memory }]
        (some (Expr.call (Expr.ident "sfn") [])),
      Stmt.varDecl [{ name := some "s", ty := some Ty.string, location := some DataLocation.memory }]
        (some (scat [Arg.positional (Expr.literal (Literal.string "a")),
                     Arg.positional (Expr.ident "h0")])),
      Stmt.returnValues (some
        (Expr.binary BinaryOp.add
          (Expr.member
            (Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.ident "s")]) "length")
          (Expr.ident "tr"))) ]) }

-- Variant: concat of two plain string locals in a varDecl init (no literal).
private def runManual2Fn : ContractItem := ContractItem.function
  { name := some "runManual2", visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [
      Stmt.varDecl [{ name := some "h0", ty := some Ty.string, location := some DataLocation.memory }]
        (some (Expr.literal (Literal.string "x"))),
      Stmt.varDecl [{ name := some "s", ty := some Ty.string, location := some DataLocation.memory }]
        (some (scat [Arg.positional (Expr.literal (Literal.string "a")),
                     Arg.positional (Expr.ident "h0")])),
      Stmt.returnValues (some
        (Expr.member
          (Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.ident "s")]) "length")) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "T", abstract := false, bases := [],
    items := [ trVar, sfnFn, runFn, runRetFn, runFirstFn, runManualFn, runManual2Fn ] }

def importedContract : ContractDecl := importedContractDecl0
def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }
def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end StringConcatCallVarDecl
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace StringConcatCallVarDecl

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.StringConcatCallVarDecl.importedContract

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StringConcatCallVarDecl.importedContractAccepted

-- The reported divergence: `string memory s = string.concat("a", sfn());`
-- solc+EVM => success, return word 6, storage slot 0 == 4. The engine formerly
-- computed Panic(0) (typeMismatch in the concat, from the un-hoisted nested call).
def run_is_w6_sto4 :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "run" State.empty [] 6 4
-- Same concat in RETURN position already lowered correctly (ANF path).
def runRet_is_w6_sto4 :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "runRet" State.empty [] 6 4
-- Side-effecting call in the FIRST concat argument (var-decl init).
def runFirst_is_w6_sto4 :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "runFirst" State.empty [] 6 4
-- Manually pre-hoisted equivalents (already lowered correctly before the fix).
def runManual_is_w6_sto4 :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "runManual" State.empty [] 6 4
def runManual2_is_w2 :=
  Examples.checkedOwnCallWordMatches 256 Fam "runManual2" State.empty [] 2

#guard accepted
#guard isOkTrue run_is_w6_sto4
#guard isOkTrue runRet_is_w6_sto4
#guard isOkTrue runFirst_is_w6_sto4
#guard isOkTrue runManual_is_w6_sto4
#guard isOkTrue runManual2_is_w2

end StringConcatCallVarDecl
end Witness
end Solidity
end SolidCore

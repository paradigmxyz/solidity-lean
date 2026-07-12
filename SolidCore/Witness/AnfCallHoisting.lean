import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
ANF-CALL-HOISTING FAMILY — the general A-normal-form call-hoisting fallback pass
(`Stmt.anfPreprocess` / `Expr.anfHoist` in `Interface.lean`) closes a whole
combinatorial family of accepted-but-unlowerable programs: any value-returning
internal / library / external single-return call NESTED in an arbitrary
expression position that the enumerated per-shape hoisters did not cover.

Each witness below is one gap cell from the rearchitecture plan (§3.1). All
callees are pure/deterministic, so the expected runtime words are the standard
ABI encodings / arithmetic that real solc 0.8.35 + the EVM produce:

  g()   returns uint256(3)      h()   returns uint256(5)
  gidx() returns uint256(1)     dbl(x) returns x*2
  gb()  returns bytes 0x01      gs()  returns string "x"
  arr() returns uint256[3] [10,20,30]     mk() returns S{a:42,b:7}

  encPacked  abi.encodePacked(g())              => 32-byte word 3
  encTwo1g   abi.encode(uint256(1), g())        => words 1, 3
  encGH      abi.encode(g(), h())               => words 3, 5   (left-to-right)
  encTernG   abi.encode(true ? g() : 2)         => word 3       (taken branch)
  encTern2   abi.encode(uint256(1), true?g():2) => words 1, 3
  bcatG      bytes.concat(g())                  => 0x01
  scatGy     string.concat(g(), "y")            => "xy"
  arrIdx1    arr()[1]                            => 20   (call as index base)
  arrIdxG    arr()[gidx()]                       => 20   (call in base and key)
  mkA        mk().a                              => 42   (call as member base)
  delAt      delete s[gidx()] then read s[0]     => 7    (call in delete index)
  cTernDbl   c ? dbl(g()) : 1                    => 6 (c) / 1 (¬c)
  cTernAri   c ? g()+1 : 2                       => 4 (c) / 2 (¬c)
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AnfCallHoisting

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def gc : Expr := Expr.call (Expr.ident "g") []
private def hc : Expr := Expr.call (Expr.ident "h") []
private def gidxc : Expr := Expr.call (Expr.ident "gidx") []
private def abiEnc (a : List Arg) : Expr := Expr.call (Expr.member (Expr.ident "abi") "encode") a
private def abiEncP (a : List Arg) : Expr := Expr.call (Expr.member (Expr.ident "abi") "encodePacked") a
private def bcat (a : List Arg) : Expr := Expr.call (Expr.member (Expr.ident "bytes") "concat") a
private def scat (a : List Arg) : Expr := Expr.call (Expr.member (Expr.ident "string") "concat") a
private def u256 (e : Expr) : Expr := Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]

private def uintRet (nm v : String) : ContractItem := ContractItem.function
  { name := some nm, visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [Stmt.returnValues (some (lit v))]) }
private def gFn := uintRet "g" "3"
private def hFn := uintRet "h" "5"
private def gidxFn := uintRet "gidx" "1"
private def dblFn : ContractItem := ContractItem.function
  { name := some "dbl", visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.ident "x") (lit "2")))]) }
private def gbFn : ContractItem := ContractItem.function
  { name := some "gb", visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.hexString "01")))]) }
private def gsFn : ContractItem := ContractItem.function
  { name := some "gs", visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.string, location := some DataLocation.memory }],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.string "x")))]) }
private def arrFn : ContractItem := ContractItem.function
  { name := some "arr", visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.array (Ty.uint 256) (some 3), location := some DataLocation.memory }],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.array [u256 (lit "10"), lit "20", lit "30"]))]) }
private def structS : ContractItem := ContractItem.structDecl
  { name := "S", fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }
private def mkFn : ContractItem := ContractItem.function
  { name := some "mk", visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.user { segments := ["S"] }, location := some DataLocation.memory }],
    body := some (Stmt.block [Stmt.returnValues (some
      (Expr.call (Expr.typeName (Ty.user { segments := ["S"] })) [Arg.positional (lit "42"), Arg.positional (lit "7")]))]) }
private def sVar : ContractItem := ContractItem.stateVar
  { name := "s", ty := Ty.array (Ty.uint 256) none, visibility := some Visibility.internal_ }
-- R2 soundness: a reverting callee used in the UNTAKEN ternary branch must NOT
-- run (its effects — here a revert — are guarded by the short-circuit).
private def revFn : ContractItem := ContractItem.function
  { name := some "rev", visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [
      Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.literal (Literal.bool false))]),
      Stmt.returnValues (some (lit "0")) ]) }
-- R4 soundness: a NARROW-return call (`uint8`) ABI-encoded must carry its
-- width cleanup into the 32-byte word.
private def narrowFn : ContractItem := ContractItem.function
  { name := some "narrow", visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.uint 8, location := none }],
    body := some (Stmt.block [Stmt.returnValues (some (lit "255"))]) }

private def extBytes (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { name := some nm, visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }
private def extStr (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { name := some nm, visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.string, location := some DataLocation.memory }],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }
private def extU (nm : String) (e : Expr) : ContractItem := ContractItem.function
  { name := some nm, visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [Stmt.returnValues (some e)]) }
private def extUc (nm : String) (body : List Stmt) : ContractItem := ContractItem.function
  { name := some nm, visibility := some Visibility.external_, mutability := StateMutability.nonpayable,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block body) }

private def delAtFn : ContractItem := ContractItem.function
  { name := some "delAt", visibility := some Visibility.external_, mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    body := some (Stmt.block [
      Stmt.expr (Expr.call (Expr.member (Expr.ident "s") "push") [Arg.positional (lit "7")]),
      Stmt.expr (Expr.call (Expr.member (Expr.ident "s") "push") [Arg.positional (lit "9")]),
      Stmt.expr (Expr.unary UnaryOp.delete (Expr.index (Expr.ident "s") gidxc)),
      Stmt.returnValues (some (Expr.index (Expr.ident "s") (lit "0"))) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "AnfCallHoisting", abstract := false, bases := [],
    items := [ gFn, hFn, gidxFn, dblFn, gbFn, gsFn, arrFn, structS, mkFn, sVar, revFn, narrowFn,
      extBytes "encPacked" (abiEncP [Arg.positional gc]),
      extBytes "encTwo1g" (abiEnc [Arg.positional (u256 (lit "1")), Arg.positional gc]),
      extBytes "encGH" (abiEnc [Arg.positional gc, Arg.positional hc]),
      extBytes "encTernG" (abiEnc [Arg.positional (Expr.ternary (Expr.literal (Literal.bool true)) gc (lit "2"))]),
      extBytes "encTern2" (abiEnc [Arg.positional (u256 (lit "1")), Arg.positional (Expr.ternary (Expr.literal (Literal.bool true)) gc (lit "2"))]),
      extBytes "bcatG" (bcat [Arg.positional (Expr.call (Expr.ident "gb") [])]),
      extStr "scatGy" (scat [Arg.positional (Expr.call (Expr.ident "gs") []), Arg.positional (Expr.literal (Literal.string "y"))]),
      extU "arrIdx1" (Expr.index (Expr.call (Expr.ident "arr") []) (lit "1")),
      extU "arrIdxG" (Expr.index (Expr.call (Expr.ident "arr") []) gidxc),
      extU "mkA" (Expr.member (Expr.call (Expr.ident "mk") []) "a"),
      delAtFn,
      extUc "cTernDbl" [Stmt.returnValues (some (Expr.ternary (Expr.ident "c") (Expr.call (Expr.ident "dbl") [Arg.positional gc]) (lit "1")))],
      extUc "cTernAri" [Stmt.returnValues (some (Expr.ternary (Expr.ident "c") (Expr.binary BinaryOp.add gc (lit "1")) (lit "2")))],
      extUc "condRev" [Stmt.returnValues (some (Expr.ternary (Expr.ident "c") gc (Expr.call (Expr.ident "rev") [])))],
      extBytes "encNarrow" (abiEnc [Arg.positional (Expr.call (Expr.ident "narrow") [])]) ] }

def importedContract : ContractDecl := importedContractDecl0
def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }
def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AnfCallHoisting
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AnfCallHoisting

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.AnfCallHoisting.importedContract

private def w32 (n : Nat) : List Nat := SolidCore.Solidity.Source.wordToBytesBE 32 n
private def bTrue : List CoreValue := [Value.word 1]
private def bFalse : List CoreValue := [Value.word 0]
private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool := SolidCore.Solidity.SolcAstImport.AnfCallHoisting.importedContractAccepted

def encPacked_is_w3 := Examples.checkedOwnCallBytesMatches 256 Fam "encPacked" State.empty [] (w32 3)
def encTwo1g_is_w1_w3 := Examples.checkedOwnCallBytesMatches 256 Fam "encTwo1g" State.empty [] (w32 1 ++ w32 3)
def encGH_is_w3_w5 := Examples.checkedOwnCallBytesMatches 256 Fam "encGH" State.empty [] (w32 3 ++ w32 5)
def encTernG_is_w3 := Examples.checkedOwnCallBytesMatches 256 Fam "encTernG" State.empty [] (w32 3)
def encTern2_is_w1_w3 := Examples.checkedOwnCallBytesMatches 256 Fam "encTern2" State.empty [] (w32 1 ++ w32 3)
def bcatG_is_01 := Examples.checkedOwnCallBytesMatches 256 Fam "bcatG" State.empty [] [1]
def scatGy_is_xy := Examples.checkedOwnCallBytesMatches 256 Fam "scatGy" State.empty [] [120, 121]
def arrIdx1_is_20 := Examples.checkedOwnCallWordMatches 256 Fam "arrIdx1" State.empty [] 20
def arrIdxG_is_20 := Examples.checkedOwnCallWordMatches 256 Fam "arrIdxG" State.empty [] 20
def mkA_is_42 := Examples.checkedOwnCallWordMatches 256 Fam "mkA" State.empty [] 42
def delAt_is_7 := Examples.checkedOwnCallWordMatches 256 Fam "delAt" State.empty [] 7
def cTernDbl_true_is_6 := Examples.checkedOwnCallWordMatches 256 Fam "cTernDbl" State.empty bTrue 6
def cTernDbl_false_is_1 := Examples.checkedOwnCallWordMatches 256 Fam "cTernDbl" State.empty bFalse 1
def cTernAri_true_is_4 := Examples.checkedOwnCallWordMatches 256 Fam "cTernAri" State.empty bTrue 4
def cTernAri_false_is_2 := Examples.checkedOwnCallWordMatches 256 Fam "cTernAri" State.empty bFalse 2
-- R2: c=true takes the g() branch and must NOT run rev() (which reverts) => 3.
def condRev_true_is_3 := Examples.checkedOwnCallWordMatches 256 Fam "condRev" State.empty bTrue 3
-- R4: abi.encode of a uint8(255) call result => 32-byte word 255 (cleanup kept).
def encNarrow_is_w255 := Examples.checkedOwnCallBytesMatches 256 Fam "encNarrow" State.empty [] (w32 255)

#guard accepted
#guard isOkTrue encPacked_is_w3
#guard isOkTrue encTwo1g_is_w1_w3
#guard isOkTrue encGH_is_w3_w5
#guard isOkTrue encTernG_is_w3
#guard isOkTrue encTern2_is_w1_w3
#guard isOkTrue bcatG_is_01
#guard isOkTrue scatGy_is_xy
#guard isOkTrue arrIdx1_is_20
#guard isOkTrue arrIdxG_is_20
#guard isOkTrue mkA_is_42
#guard isOkTrue delAt_is_7
#guard isOkTrue cTernDbl_true_is_6
#guard isOkTrue cTernDbl_false_is_1
#guard isOkTrue cTernAri_true_is_4
#guard isOkTrue cTernAri_false_is_2
#guard isOkTrue condRev_true_is_3
#guard isOkTrue encNarrow_is_w255

end AnfCallHoisting
end Witness
end Solidity
end SolidCore

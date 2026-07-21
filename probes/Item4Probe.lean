import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 4000000

namespace Item4Probe

open SolidCore.Solidity
open SolidCore.Solidity.Source (State Value CallResult)

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def assignIdent (name : String) (rhs : Expr) : Stmt :=
  Stmt.expr (Expr.assign (Expr.ident name) AssignOp.assign rhs)
private def hexAssign (name value : String) : Stmt :=
  assignIdent name (Expr.literal (Literal.hexString value))
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

-- bytes(b)[1] : does emitted core contain a `contents` read under index?
def idxContract : ContractDecl :=
  { kind := ContractKind.contract, name := "I4A",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "b" "aabb"
          , Stmt.returnValues (some
              (Expr.call (Expr.typeName (Ty.uint 256))
                [Arg.positional
                  (Expr.call (Expr.typeName (Ty.uint 8))
                    [Arg.positional
                      (Expr.index
                        (Expr.call (Expr.typeName Ty.bytes)
                          [Arg.positional (Expr.ident "b")])
                        (lit "1"))])])) ] ] }

-- bytes(b).length
def lenContract : ContractDecl :=
  { kind := ContractKind.contract, name := "I4B",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "b" "aabb"
          , Stmt.returnValues (some
              (Expr.member
                (Expr.call (Expr.typeName Ty.bytes)
                  [Arg.positional (Expr.ident "b")])
                "length")) ] ] }

-- string(b) cast returned as string: bytes -> string
def castRetContract : ContractDecl :=
  { kind := ContractKind.contract, name := "I4C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b", ty := Ty.bytes }
      , mkRun [{ name := none, ty := Ty.string,
                 location := some DataLocation.memory }]
          [ hexAssign "b" "6869"
          , Stmt.returnValues (some
              (Expr.call (Expr.typeName Ty.string)
                [Arg.positional (Expr.ident "b")])) ] ] }

private def coreDump (decl : ContractDecl) : String :=
  match TypeCheck.CheckedInput.ownContract? decl with
  | some checked => reprStr checked.core.functions
  | none => "REJECTED"

private def occurrences (needle hay : String) : Nat :=
  (hay.splitOn needle).length - 1

#eval! ("idx contents/load/element",
  occurrences "StorageReadMode.contents" (coreDump idxContract),
  occurrences "StorageReadMode.load" (coreDump idxContract),
  occurrences "StorageReadMode.element" (coreDump idxContract))
#eval! ("len", occurrences "StorageReadMode.contents" (coreDump lenContract),
  occurrences "StorageReadMode.load" (coreDump lenContract),
  occurrences "StorageReadMode.header" (coreDump lenContract))
#eval! ("castRet", occurrences "StorageReadMode.contents" (coreDump castRetContract),
  occurrences "StorageReadMode.load" (coreDump castRetContract))

#eval TypeCheck.Examples.checkedOwnCallWordMatches 4096 idxContract "run"
  State.empty [] 0xbb
#eval TypeCheck.Examples.checkedOwnCallWordMatches 4096 lenContract "run"
  State.empty [] 2

-- Where do `contents` reads appear across a wider battery? Count in a
-- contract exercising abi.encode(bytes(b)), keccak256(bytes(b)), etc.
def encCastContract : ContractDecl :=
  { kind := ContractKind.contract, name := "I4D",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "b" "aabb"
          , Stmt.varDecl
              [{ name := some "e", ty := some Ty.bytes,
                 location := some DataLocation.memory }]
              (some (Expr.call (Expr.member (Expr.ident "abi") "encode")
                [Arg.positional
                  (Expr.call (Expr.typeName Ty.bytes)
                    [Arg.positional (Expr.ident "b")])]))
          , Stmt.returnValues (some (Expr.member (Expr.ident "e") "length")) ] ] }

#eval! ("encCast", occurrences "StorageReadMode.contents" (coreDump encCastContract),
  occurrences "StorageReadMode.load" (coreDump encCastContract))

end Item4Probe

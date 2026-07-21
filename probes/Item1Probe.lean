import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked


set_option maxHeartbeats 4000000

namespace Item1Probe

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

-- Shape A: abi.encode([b1, b2]) with storage bytes b1 b2
def shapeA : ContractDecl :=
  { kind := ContractKind.contract, name := "PA",
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
          , Stmt.returnValues (some (Expr.member (Expr.ident "e") "length")) ] ] }

-- Shape B: storage locals: bytes storage p1 = b1; abi.encode([p1, p1])
def shapeB : ContractDecl :=
  { kind := ContractKind.contract, name := "PB",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b1", ty := Ty.bytes }
      , mkRun retUint
          [ hexAssign "b1" "aa"
          , Stmt.varDecl
              [{ name := some "p1", ty := some Ty.bytes,
                 location := some DataLocation.storage }]
              (some (Expr.ident "b1"))
          , Stmt.varDecl
              [{ name := some "e", ty := some Ty.bytes,
                 location := some DataLocation.memory }]
              (some (Expr.call (Expr.member (Expr.ident "abi") "encode")
                [ Arg.positional
                    (Expr.array [Expr.ident "p1", Expr.ident "p1"]) ]))
          , Stmt.returnValues (some (Expr.member (Expr.ident "e") "length")) ] ] }

-- Shape C: string storage in array literal under keccak256(abi.encode(...))
def shapeC : ContractDecl :=
  { kind := ContractKind.contract, name := "PC",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "s1", ty := Ty.string }
      , mkRun retUint
          [ assignIdent "s1" (Expr.literal (Literal.string "hey"))
          , Stmt.varDecl
              [{ name := some "e", ty := some Ty.bytes,
                 location := some DataLocation.memory }]
              (some (Expr.call (Expr.member (Expr.ident "abi") "encode")
                [ Arg.positional
                    (Expr.array [Expr.ident "s1", Expr.ident "s1"]) ]))
          , Stmt.returnValues (some (Expr.member (Expr.ident "e") "length")) ] ] }

#eval (TypeCheck.Result.isOk
  (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit shapeA)),
  TypeCheck.Result.isOk
  (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit shapeB)),
  TypeCheck.Result.isOk
  (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit shapeC)))

-- abi.encode(bytes[2]): 0x20 | off1 0x40 | off2 0x80 | len 1 | "aa" | len 2 | "bbcc"
-- = 7*32 = 224
#eval TypeCheck.Examples.checkedOwnCallWordMatches 4096 shapeA "run"
  State.empty [] 224

-- abi.encode(bytes[2]) both "aa": 0x20 | 0x40 | 0x80 | 1 | aa | 1 | aa = 224
#eval TypeCheck.Examples.checkedOwnCallWordMatches 4096 shapeB "run"
  State.empty [] 224

-- abi.encode(string[2]) both "hey": same layout = 224
#eval TypeCheck.Examples.checkedOwnCallWordMatches 4096 shapeC "run"
  State.empty [] 224

end Item1Probe

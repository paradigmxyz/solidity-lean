import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
MSG-SHADOW-STRUCT-LOCAL — a local variable named `msg` SHADOWS the `msg` magic
global, so `msg.<member>` is an ordinary struct field access, not the
`msg.value` builtin.

```solidity
contract T {
    struct M { uint256 value; }
    function run() public returns (uint256) {
        M memory msg; msg.value = 9;
        return msg.value;
    }
}
```

solc 0.8.35 accepts this and `run()` returns 9: the local `M memory msg`
shadows the `msg` magic global, so `msg.value` reads the struct's `value`
field. solidity-lean formerly failed closed in the type checker with
`mutabilityViolation "msg.value in a non-payable function"`: the
`Expr.member (Expr.ident "msg") member` arm matched the magic global
UNCONDITIONALLY, applying the G2 payable-mutability obligation (and the
`msg.value` builtin type) even when `msg` was a shadowing local — an
over-rejection of an in-scope, solc-accepted program.

The fix (`SolidCore/Solidity/TypeCheck.lean`) guards that arm on
`env.lookupVar? "msg"`: an unshadowed `msg` keeps the magic-global handling
(extracted to `checkMsgGlobalMember`); a shadowing local routes `msg.<member>`
through the ordinary struct-field member path (no payable obligation, field
type). The lowering already rewrites `msg.value` -> `msg[0]` via
`resolveStructs` (the local `msg` is in its `typeEnv`), so execution reads the
memory struct field and returns 9.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace MsgShadowStructLocal

open SolidCore.Solidity.Source

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
    { name := "M",
      fields := [{ name := "value", ty := Ty.uint 256 }] }),
    (ContractItem.function
    { kind := FunctionKind.function,
      name := some "run",
      visibility := some Visibility.public_,
      mutability := StateMutability.nonpayable,
      params := [],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false,
      override? := none,
      modifiers := [],
      body := some (Stmt.block [Stmt.varDecl [{ name := some "msg", ty := Ty.user ({ segments := ["M"] }), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.member (Expr.ident "msg") "value") AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.member (Expr.ident "msg") "value"))]) })] }

def importedContract : ContractDecl := importedContractDecl0

def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Call `fn` (no args) on the harness against empty state; `none` on any
    lowering/execution failure. -/
def callWords? (fn : String) : Option (List SolidCore.Solidity.Source.Word) :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match
          TypeCheck.CheckedProgram.callContract 1000 program
            "T"
            (SolidCore.Solidity.Source.CallTarget.name fn)
            SolidCore.Solidity.Source.State.empty [] with
      | Except.ok (SolidCore.Solidity.Source.CallResult.returned _ values) =>
          values.mapM (fun v =>
            match v with
            | SolidCore.Solidity.Source.Value.word w => some w
            | _ => none)
      | _ => none
  | _ => none

end MsgShadowStructLocal
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace MsgShadowStructLocal

open SolidCore.Solidity.SolcAstImport.MsgShadowStructLocal

/-- The harness is ACCEPTED by the checker (was over-rejected). -/
def accepted : Bool := importedContractAccepted

def returns (fn : String) (expected : List Nat) : Bool :=
  match callWords? fn with
  | some ws =>
      ws.length == expected.length &&
        (ws.zip expected).all (fun (w, e) =>
          SolidCore.Solidity.Source.wordEq w (e : SolidCore.Solidity.Source.Word))
  | none => false

/-- The core fix: `run()` reads the shadowing struct local's `value` field. -/
def runReturns9 : Bool := returns "run" [9]

#guard accepted
#guard runReturns9

end MsgShadowStructLocal
end Witness
end Solidity
end SolidCore

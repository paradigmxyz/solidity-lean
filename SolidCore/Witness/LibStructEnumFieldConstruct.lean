import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
LIB-STRUCT-ENUM-FIELD-CONSTRUCT — constructing a struct declared in a LIBRARY
whose field type is another type from that SAME library now type-checks and
EXECUTES.

```solidity
library Lib {
    enum Mode { Off, Slow, Fast }
    struct S { Mode m; }
}
contract T {
    function f(uint8 x) external pure returns (uint8) {
        Lib.S memory s = Lib.S(Lib.Mode(x));
        return uint8(s.m);
    }
}
```

solc 0.8.35 accepts this and `f(1)` returns `1`. The model's CHECKER
over-rejected: the struct-constructor argument check qualified the field target
types (`StructDecl.fieldTys`) through `env.qualifyCurrentLocalUserTypes`, i.e.
the CURRENT contract's scope (`T`). For a struct declared in library `Lib`, the
bare field type `Mode` is not a local type of `T`, so it stayed unqualified
(`Ty.user ["Mode"]`), while the argument `Lib.Mode(x)` carried the fully
qualified `Ty.user ["Lib", "Mode"]`. The two mismatched and the whole program
failed closed with `TypeError.expectedType (user ["Mode"]) (user ["Lib","Mode"])`.

The fix (SolidCore/Solidity/TypeCheck.lean): qualify the field target types
through the struct's OWN declaring scope, `env.qualifyStructFieldTy path`, the
same normalization the struct-member-access sites already use. For a
contract-local struct the declaring scope IS the current contract, so
`new Node[](n)`-style element matching (#163) is preserved; for a
library/other-contract struct the field type is now qualified to the declaring
scope and matches the argument.

Booleans `#eval`-confirmed and pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LibStructEnumFieldConstruct

open SolidCore.Solidity

def libDecl : ContractDecl :=
{ kind := ContractKind.library
  name := "Lib"
  items :=
    [ ContractItem.enumDecl { name := "Mode", cases := ["Off", "Slow", "Fast"] }
    , ContractItem.structDecl
        { name := "S"
          fields := [{ name := "m", ty := Ty.user { segments := ["Mode"] } }] } ] }

def tDecl : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  items :=
    [ ContractItem.function
        { kind := FunctionKind.function
          name := some "f"
          visibility := some Visibility.external_
          mutability := StateMutability.pure
          params := [{ name := some "x", ty := Ty.uint 8, location := none }]
          returns := [{ name := none, ty := Ty.uint 8, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.varDecl
                [{ name := some "s", ty := Ty.user { segments := ["Lib", "S"] },
                   location := some DataLocation.memory }]
                (some (Expr.call
                  (Expr.typeName (Ty.user { segments := ["Lib", "S"] }))
                  [Arg.positional (Expr.call
                    (Expr.typeName (Ty.user { segments := ["Lib", "Mode"] }))
                    [Arg.positional (Expr.ident "x")])]))
            , Stmt.returnValues (some (Expr.call
                (Expr.typeName (Ty.uint 8))
                [Arg.positional (Expr.member (Expr.ident "s") "m")])) ]) } ] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
      SourceItem.contract libDecl, SourceItem.contract tDecl] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Call `f(x)` on `T` against empty state and return the single word produced;
    `none` on any lowering/execution failure. -/
def callWord? (x : Nat) : Option SolidCore.Solidity.Source.Word :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match
          TypeCheck.CheckedProgram.callContract 1000 program "T"
            (SolidCore.Solidity.Source.CallTarget.name "f")
            SolidCore.Solidity.Source.State.empty
            [SolidCore.Solidity.Source.Value.word (x : SolidCore.Solidity.Source.Word)] with
      | Except.ok (SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word w]) => some w
      | _ => none
  | _ => none

end LibStructEnumFieldConstruct
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace LibStructEnumFieldConstruct

open SolidCore.Solidity.SolcAstImport.LibStructEnumFieldConstruct

/-- The program (library-declared struct with a library-local enum field type,
    constructed from a contract) is ACCEPTED by the checker. -/
def accepted : Bool := importedContractAccepted

/-- `f(x)` executes and returns `expected`. -/
def returns (x expected : Nat) : Bool :=
  match callWord? x with
  | some w =>
      SolidCore.Solidity.Source.wordEq w (expected : SolidCore.Solidity.Source.Word)
  | none => false

#guard accepted
#guard returns 1 1
#guard returns 2 2
#guard returns 0 0

end LibStructEnumFieldConstruct
end Witness
end Solidity
end SolidCore

import SolidCore.Refinement.Generic.SourceCall
import SolidCore.Solidity.Interface.Contracts

/-!
# The generic erasure of a public mapping getter

A regression for the generic check's erasure of the getter SolidCore builds for a public word
mapping. For `mapping(address => uint256) public balanceOf`, SolidCore's interface
(`StateVarDecl.toCoreRecursiveGetterIfPublic?`, through `StateVarDecl.publicGetterBodyExpr`)
builds the function `balanceOf(address)` whose body returns `storagePath "balanceOf" [_key0]`,
that is `.storageRead .load "balanceOf" [.var "_key0"]`. `eraseExpr` used to erase only the
`.element` read of a mapping, so `eraseFn` of the getter was `none` and the generic probe
reported `source tree undefined (erasure)` for `balanceOf(address)`.

* `getter_body`: the getter's body is the `.load` read of the mapping at `_key0`;
* `erase_load`: `eraseExpr` erases that read to the writes' read of `hash key slot`, the same
  word as the `.element` read (`erase_element`);
* `erase_getter`: `eraseFn` erases the whole getter;
* the refusals: a `.load` read of a mapping to `bool` (`refuse_bool_map`: `mapOf?` admits only
  `uint256` values) and the two-key `.load` path of a nested mapping's getter (`refuse_nested`
  and `refuse_nested_getter`: the arm takes exactly one key) stay `none`.
-/

namespace SolidCore.Refinement.Generic.EraseLoadTest

open SolidCore.Solidity.Source

/-- The storage of the test: a word mapping at slot 2, a mapping to `bool` at slot 3 and a nested
word mapping at slot 4, with SolidCore's core layouts. -/
def fields : List StorageField :=
  [{ name := "balanceOf", slot := 2, layout? := some (.mapping .address (.scalar .uint256)) },
   { name := "isMinter", slot := 3, layout? := some (.mapping .address (.scalar .bool)) },
   { name := "allowance", slot := 4,
     layout? := some (.mapping .address (.mapping .address (.scalar .uint256))) }]

/-- The erasure environment of the test. -/
def env : EraseEnv := { fields := fields, events := [], tbl := [] }

/-- `mapping(address => uint256) public balanceOf;` -/
def balanceOfDecl : SolidCore.Solidity.StateVarDecl :=
  { name := "balanceOf", ty := .mapping (.address false) (.uint 256), visibility := some .public_ }

/-- `mapping(address => mapping(address => uint256)) public allowance;` -/
def allowanceDecl : SolidCore.Solidity.StateVarDecl :=
  { name := "allowance", ty := .mapping (.address false) (.mapping (.address false) (.uint 256)),
    visibility := some .public_ }

/-- The getter SolidCore builds for a public state variable of the test. -/
def getter? (d : SolidCore.Solidity.StateVarDecl) : Option FunctionDef :=
  (SolidCore.Solidity.Executable.StateVarDecl.toCoreRecursiveGetterIfPublic?
    ["balanceOf", "isMinter", "allowance"] d).bind id

/-- A state whose local `k` holds argument word 0. -/
def S0 : SymState := { scopes := [[("k", .arg 0)]], writes := [], logs := [] }

theorem getter_body :
    (getter? balanceOfDecl).map (·.body) =
      some (.returnValues [.storageRead .load "balanceOf" [.var "_key0"]]) := rfl

theorem erase_load :
    eraseExpr fields S0 (.storageRead .load "balanceOf" [.var "k"]) =
      some ([], S0.writes.read (.hash (.arg 0) (.lit 2))) := by decide +kernel

theorem erase_element :
    eraseExpr fields S0 (.storageRead .element "balanceOf" [.var "k"]) =
      eraseExpr fields S0 (.storageRead .load "balanceOf" [.var "k"]) := by decide +kernel

theorem erase_getter : ((getter? balanceOfDecl).bind (eraseFn env 64)).isSome = true := by
  decide +kernel

/-- Refusal: `mapOf?` admits only mappings to `uint256`, so the `.load` read of a mapping to
`bool` erases to nothing. -/
theorem refuse_bool_map :
    eraseExpr fields S0 (.storageRead .load "isMinter" [.var "k"]) = none := by decide +kernel

/-- Refusal: the `.load` arm takes exactly one key, so the two-key path of a nested mapping's
getter erases to nothing. -/
theorem refuse_nested :
    eraseExpr fields S0 (.storageRead .load "allowance" [.var "k", .var "k"]) = none := by
  decide +kernel

theorem refuse_nested_getter :
    ((getter? allowanceDecl).bind (eraseFn env 64)).isNone = true := by decide +kernel

#print axioms loadPath_eq_loadIndex
#print axioms loadPath_map
#print axioms eval_erase
#print axioms erase_getter
#print axioms refuse_nested_getter

#eval (getter? balanceOfDecl).map (·.body)
#eval (getter? balanceOfDecl).bind (eraseFn env 64)
#eval eraseExpr fields S0 (.storageRead .load "balanceOf" [.var "k"])
#eval eraseExpr fields S0 (.storageRead .load "isMinter" [.var "k"])
#eval eraseExpr fields S0 (.storageRead .load "allowance" [.var "k", .var "k"])
#eval (getter? allowanceDecl).map (·.body)
#eval (getter? allowanceDecl).bind (eraseFn env 64)

end SolidCore.Refinement.Generic.EraseLoadTest

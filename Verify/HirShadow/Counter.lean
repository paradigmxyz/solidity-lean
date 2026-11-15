import Contracts.VerifyCounter.SourceAst
import Verify.HirShadow.Check
import Verify.HirShadow.Counter.Facts

/-!
# solar's HIR shadow of Counter agrees with its solc-AST source model

`Counter` is solar-verify's example (`Certified/verify_counter/verify_counter.sol`), whose source
model `importedContract` is solc 0.8.35's AST through `scripts/solc_ast_to_lean_source.py`
(`Contracts/VerifyCounter/SourceAst.lean`). `Counter/Facts.lean` is what solar's analysis states
about the same file (`Counter/hir_shadow.json`, written by solar's `tools/hir-shadow/hir_shadow.py`).

* `agrees`: `check` accepts the facts: the same storage slots, offsets and types, and the same
  functions, getters and constructor with the same signatures, visibility, mutability, ABI types,
  and selectors that are Keccak-256 of the signatures the source model gives.
* The negatives change one fact each (a slot, a selector, a type, an order, the contract, the
  version) and are rejected; a source model outside the envelope is blocked, never agreed.

The facts are hints: the source model stays the source of truth, and agreement is evidence that
two independent frontends read the interface alike, not a proof of either.
-/

namespace Verify.HirShadow.Counter
open Verify.HirShadow SolidCore.Solidity

abbrev decl : ContractDecl := SolidCore.Refinement.Source.VerifyCounter.importedContract
abbrev keccakSel : String → Nat := SolidCore.Solidity.Source.Keccak.selector4

theorem agrees_by_table : check selectorTable decl facts = .agree := by decide +kernel

theorem agrees : check keccakSel decl facts = .agree := by
  rw [show keccakSel = selectorTable from selector_eq]; exact agrees_by_table

def wrongSlot : Facts :=
  { facts with stateVars := facts.stateVars.map fun v => if v.name = "limit" then { v with slot := 0 } else v }
def wrongSelector : Facts :=
  { facts with functions := facts.functions.map fun f =>
      if f.name = "bump" then { f with selector := f.selector.map (· + 1) } else f }
def wrongType : Facts :=
  { facts with stateVars := facts.stateVars.map fun v => if v.name = "count" then { v with type := "uint128" } else v }
def wrongOrder : Facts := { facts with functions := facts.functions.reverse }
def wrongContract : Facts := { facts with contract := "Other" }
def wrongVersion : Facts := { facts with version := 2 }

theorem wrongSlot_rejected : (check selectorTable decl wrongSlot).isAgree = false := by decide +kernel
theorem wrongSelector_rejected : (check selectorTable decl wrongSelector).isAgree = false := by decide +kernel
theorem wrongType_rejected : (check selectorTable decl wrongType).isAgree = false := by decide +kernel
theorem wrongOrder_rejected : (check selectorTable decl wrongOrder).isAgree = false := by decide +kernel
theorem wrongContract_rejected : (check selectorTable decl wrongContract).isAgree = false := by decide +kernel
theorem wrongVersion_rejected : (check selectorTable decl wrongVersion).isAgree = false := by decide +kernel

/-- The source model with a mapping added: outside the envelope. -/
def withMapping : ContractDecl :=
  { decl with items := decl.items ++
      [.stateVar { name := "m", ty := .mapping (.address false) (.uint 256) }] }

theorem withMapping_blocked :
    check selectorTable withMapping facts = .blocked "state variable m is not of a value type" := by
  decide +kernel

end Verify.HirShadow.Counter

import Contracts.Reader.Source
import SolidCore.Refinement.KernelRfl
import Verify.VC.KernelIdx

/-!
# SolidCore's checked `Reader`

The kernel's type check of `Reader` (`contract_ok`), with the checker's selectors from a table
each of whose entries the kernel checks against Keccak-256 once (`selector_eq`). The selectors
are solc 0.8.35's `--hashes` of `Certified/reader/reader.sol`.
-/

namespace SolidCore.Verify.VC.Reader

open SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- SolidCore's checked `Reader`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract SolidCore.Verify.VC.Source.Reader.importedSourceUnit "Reader"

/-- The selector of `price()`. -/
abbrev priceSel : Nat := 2687873534

/-- The selector of `price()`, by Keccak-256 of its signature. -/
def selPrice : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "price()"

kernel_rfl selPrice_eq selPrice priceSel

/-- The selector of `read(address)`. -/
abbrev readSel : Nat := 2693245054

/-- The selector of `read(address)`, by Keccak-256 of its signature. -/
def selRead : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "read(address)"

kernel_rfl selRead_eq selRead readSel

/-- `ABI.selectorFromSignature`, with `Reader`'s selectors by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "price()" then priceSel
  else if s = "read(address)" then readSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  by_cases h0 : s = "price()"
  · rw [ite_eq_left h0, h0]
    exact selPrice_eq
  rw [ite_eq_right h0]
  by_cases h1 : s = "read(address)"
  · rw [ite_eq_left h1, h1]
    exact selRead_eq
  rw [ite_eq_right h1]

/-- Whether SolidCore type checks the contract. -/
def accepted : Bool :=
  match contract? with
  | .ok _ => true
  | .error _ => false

kernel_rfl accepted_eq accepted true using selector_eq SolidCore.Verify.VC.mkIdx_eq

/-- SolidCore type checks `Reader`. -/
theorem contract_ok : ∃ c, contract? = .ok c := by
  have h := accepted_eq
  unfold accepted at h
  split at h
  · next c hc => exact ⟨c, hc⟩
  · simp at h

/-- info: 'SolidCore.Verify.VC.Reader.contract_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contract_ok

end SolidCore.Verify.VC.Reader

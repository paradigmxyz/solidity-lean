-- Generated from Contracts/CallFamilies/Calls.sol's signatures (solc 0.8.35 --hashes). Do not edit.

import Contracts.CallFamilies.Source
import SolidCore.Refinement.KernelRfl
import Verify.VC.KernelIdx

/-!
# SolidCore's checked `Calls`

The kernel's type check of `Calls` (`contract_ok`), with the checker's
selectors from a table each of whose entries the kernel checks against Keccak-256 once
(`selector_eq`).
-/

namespace SolidCore.Verify.VC.Calls

open SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- SolidCore's checked `Calls`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract SolidCore.Verify.VC.Source.Calls.importedSourceUnit "Calls"

/-- The selector of `balanceOf(address)`. -/
abbrev balanceOfSel : Nat := 1889567281

/-- The selector of `balanceOf(address)`, by Keccak-256 of its signature. -/
def selBalanceOf : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "balanceOf(address)"

kernel_rfl selBalanceOf_eq selBalanceOf balanceOfSel

/-- The selector of `factory()`. -/
abbrev factorySel : Nat := 3294232917

/-- The selector of `factory()`, by Keccak-256 of its signature. -/
def selFactory : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "factory()"

kernel_rfl selFactory_eq selFactory factorySel

/-- The selector of `feeOn()`. -/
abbrev feeOnSel : Nat := 1328766218

/-- The selector of `feeOn()`, by Keccak-256 of its signature. -/
def selFeeOn : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "feeOn()"

kernel_rfl selFeeOn_eq selFeeOn feeOnSel

/-- The selector of `feeTo()`. -/
abbrev feeToSel : Nat := 25067096

/-- The selector of `feeTo()`, by Keccak-256 of its signature. -/
def selFeeTo : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "feeTo()"

kernel_rfl selFeeTo_eq selFeeTo feeToSel

/-- The selector of `flash(address,uint256,bytes)`. -/
abbrev flashSel : Nat := 4148228904

/-- The selector of `flash(address,uint256,bytes)`, by Keccak-256 of its signature. -/
def selFlash : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "flash(address,uint256,bytes)"

kernel_rfl selFlash_eq selFlash flashSel

/-- The selector of `kLast()`. -/
abbrev kLastSel : Nat := 1952775229

/-- The selector of `kLast()`, by Keccak-256 of its signature. -/
def selKLast : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "kLast()"

kernel_rfl selKLast_eq selKLast kLastSel

/-- The selector of `onFlash(address,uint256,bytes)`. -/
abbrev onFlashSel : Nat := 1971785435

/-- The selector of `onFlash(address,uint256,bytes)`, by Keccak-256 of its signature. -/
def selOnFlash : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "onFlash(address,uint256,bytes)"

kernel_rfl selOnFlash_eq selOnFlash onFlashSel

/-- The selector of `reserve()`. -/
abbrev reserveSel : Nat := 3442643934

/-- The selector of `reserve()`, by Keccak-256 of its signature. -/
def selReserve : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "reserve()"

kernel_rfl selReserve_eq selReserve reserveSel

/-- The selector of `skim(address)`. -/
abbrev skimSel : Nat := 3156594551

/-- The selector of `skim(address)`, by Keccak-256 of its signature. -/
def selSkim : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "skim(address)"

kernel_rfl selSkim_eq selSkim skimSel

/-- The selector of `sync()`. -/
abbrev syncSel : Nat := 4294363881

/-- The selector of `sync()`, by Keccak-256 of its signature. -/
def selSync : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "sync()"

kernel_rfl selSync_eq selSync syncSel

/-- The selector of `token()`. -/
abbrev tokenSel : Nat := 4228666474

/-- The selector of `token()`, by Keccak-256 of its signature. -/
def selToken : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "token()"

kernel_rfl selToken_eq selToken tokenSel

/-- `ABI.selectorFromSignature`, with `Calls`'s selectors by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "balanceOf(address)" then balanceOfSel
  else if s = "factory()" then factorySel
  else if s = "feeOn()" then feeOnSel
  else if s = "feeTo()" then feeToSel
  else if s = "flash(address,uint256,bytes)" then flashSel
  else if s = "kLast()" then kLastSel
  else if s = "onFlash(address,uint256,bytes)" then onFlashSel
  else if s = "reserve()" then reserveSel
  else if s = "skim(address)" then skimSel
  else if s = "sync()" then syncSel
  else if s = "token()" then tokenSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  by_cases h0 : s = "balanceOf(address)"
  · rw [ite_eq_left h0, h0]
    exact selBalanceOf_eq
  rw [ite_eq_right h0]
  by_cases h1 : s = "factory()"
  · rw [ite_eq_left h1, h1]
    exact selFactory_eq
  rw [ite_eq_right h1]
  by_cases h2 : s = "feeOn()"
  · rw [ite_eq_left h2, h2]
    exact selFeeOn_eq
  rw [ite_eq_right h2]
  by_cases h3 : s = "feeTo()"
  · rw [ite_eq_left h3, h3]
    exact selFeeTo_eq
  rw [ite_eq_right h3]
  by_cases h4 : s = "flash(address,uint256,bytes)"
  · rw [ite_eq_left h4, h4]
    exact selFlash_eq
  rw [ite_eq_right h4]
  by_cases h5 : s = "kLast()"
  · rw [ite_eq_left h5, h5]
    exact selKLast_eq
  rw [ite_eq_right h5]
  by_cases h6 : s = "onFlash(address,uint256,bytes)"
  · rw [ite_eq_left h6, h6]
    exact selOnFlash_eq
  rw [ite_eq_right h6]
  by_cases h7 : s = "reserve()"
  · rw [ite_eq_left h7, h7]
    exact selReserve_eq
  rw [ite_eq_right h7]
  by_cases h8 : s = "skim(address)"
  · rw [ite_eq_left h8, h8]
    exact selSkim_eq
  rw [ite_eq_right h8]
  by_cases h9 : s = "sync()"
  · rw [ite_eq_left h9, h9]
    exact selSync_eq
  rw [ite_eq_right h9]
  by_cases h10 : s = "token()"
  · rw [ite_eq_left h10, h10]
    exact selToken_eq
  rw [ite_eq_right h10]

/-- Whether SolidCore type checks the contract. -/
def accepted : Bool :=
  match contract? with
  | .ok _ => true
  | .error _ => false

kernel_rfl accepted_eq accepted true using selector_eq SolidCore.Verify.VC.mkIdx_eq

/-- SolidCore type checks `Calls`. -/
theorem contract_ok : ∃ c, contract? = .ok c := by
  have h := accepted_eq
  unfold accepted at h
  split at h
  · next c hc => exact ⟨c, hc⟩
  · simp at h

/-- info: 'SolidCore.Verify.VC.Calls.contract_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contract_ok

end SolidCore.Verify.VC.Calls

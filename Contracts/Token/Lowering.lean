import Contracts.Token.VC.Transfer
import SolidCore.Refinement.Generic.Stage
import verify_token.gen.Token.Stage0

/-!
# solar-verify's Token: the generic source stage to solar's first lowered MIR

SolidCore's checked `Token` (`SolidCore.Verify.VC.Token.contract?`, solc 0.8.35's AST of
scripts/verify/Token.sol through scripts/solc_ast_to_lean_source.py into Contracts/Token/VC/Source.lean;
Certified/verify_token/verify_token.sol is the same file byte for byte) against
`SolarTV.Export.Token.stage0`, solar's first lowered MIR module of that source after
`lower-evm-shaped` (Certified/verify_token/gen, -Ogas, osaka), the module Certified/verify_token's
backend stages start from.

`Generic.check` erases each external function of the SolidCore contract to a tree, runs the module
symbolically on its selector with the environment flags (the caller is `callerWord`, a mapping slot
the word `solHash key slot`), and compares the trees in canonical form. The kernel evaluates it
from the source text up (`kernel_rfl`, with the selectors and the hash-map index by table, each
entry checked against Keccak-256 or its definition once), one function at a time.

* `check_*_eq`: the check accepts stage0 for `transfer`, `burn` and the other external functions.
* `stage`: for each of them, the stage from SolidCore to stage0 on solar-verify's binding scope
  `stageScope fn [(2, 4096)]` (any argument words, no value, any storage that writes the slot the
  constructor wrote), under every oracle with SolidCore's caller and hash of two words.
* `check_rejects_*`: the check rejects stage0 with `transfer`'s recipient credit dropped and with
  `burn`'s total-supply write sent to another slot.
-/

namespace SolidCore.Refinement.Solar.VerifyTokenSource

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity SolidCore.Verify.VC.Token
open SolarTV.Export.Token (stage0)

/-- The steps along each path of the symbolic run of the module. -/
def mirFuel : Nat := 40

/-- `balanceOf(address)`, the mapping's getter, as the stage's ABI sees it. -/
def fnBalanceOf : Fn := ⟨balanceofSel, [.uint 256]⟩

/-- `totalSupply()`. -/
def fnTotalSupply : Fn := ⟨totalsupplySel, []⟩

/-- `owner()`. -/
def fnOwner : Fn := ⟨ownerSel, []⟩

/-- `mint(address,uint256)`. -/
def fnMint : Fn := ⟨mintSel, [.uint 256, .uint 256]⟩

/-- Whether the generic check accepts stage0 for `fn` against SolidCore's checked `Token`. -/
def checkOn (m : SolarTV.MIR.Lowered.Module) (fn : Fn) : Option Bool :=
  match contract? with
  | .ok c => some (Generic.check fuel mirFuel c.core m [fn] .all)
  | .error _ => none



/-- The check on stage0, for each function. -/
def transferOk? : Option Bool := checkOn stage0 fnTransfer
def burnOk? : Option Bool := checkOn stage0 fnBurn
def mintOk? : Option Bool := checkOn stage0 fnMint
def totalSupplyOk? : Option Bool := checkOn stage0 fnTotalSupply
def ownerOk? : Option Bool := checkOn stage0 fnOwner

-- Each by the kernel's conversion check, from the source text up.
kernel_rfl check_transfer_eq transferOk? (some true) using SolidCore.Verify.VC.Token.selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl check_burn_eq burnOk? (some true) using SolidCore.Verify.VC.Token.selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl check_mint_eq mintOk? (some true) using SolidCore.Verify.VC.Token.selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl check_totalSupply_eq totalSupplyOk? (some true) using SolidCore.Verify.VC.Token.selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl check_owner_eq ownerOk? (some true) using SolidCore.Verify.VC.Token.selector_eq SolidCore.Verify.VC.mkIdx_eq

/-! ## Mutants the check rejects -/

/-- stage0 with each instruction of function `i` changed by `f`. -/
def mapFn (i : Nat) (f : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst) :
    SolarTV.MIR.Lowered.Module :=
  { stage0 with
    functions := stage0.functions.mapIdx fun j fn =>
      if j = i then { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } }
      else fn }

/-- `transfer` storing the recipient's old balance back instead of the credited one. -/
def dropCredit : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none .sstore [.value 58, .value 27] => .effect none .sstore [.value 58, .value 20]
  | i => i

/-- `burn` writing the new total supply to slot 2 (`owner`) instead of slot 1. -/
def wrongSupplySlot : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none .sstore [.const 1, .value 18] => .effect none .sstore [.const 2, .value 18]
  | i => i

def transferMutantOk? : Option Bool := checkOn (mapFn 5 dropCredit) fnTransfer
def burnMutantOk? : Option Bool := checkOn (mapFn 6 wrongSupplySlot) fnBurn

kernel_rfl check_rejects_dropCredit transferMutantOk? (some false) using SolidCore.Verify.VC.Token.selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl check_rejects_wrongSupplySlot burnMutantOk? (some false) using SolidCore.Verify.VC.Token.selector_eq SolidCore.Verify.VC.mkIdx_eq

/-! ## The stage -/

theorem check_of {fn : Fn} {c : TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (h : checkOn stage0 fn = some true) :
    Generic.check fuel mirFuel c.core stage0 [fn] .all = true := by
  simp only [checkOn, hc, Option.some.injEq] at h
  exact h

/-- The constructor leaves `owner` (slot 2) as SolidCore's deployer, 4096, and no logs. -/
theorem deployed {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ∃ d, Wide.DeployedAt fuel c d [(2, 4096)] := by
  have hshape := burnShape_eq
  simp only [burnShape?, hc, Option.some.injEq, Prod.mk.injEq] at hshape
  exact Wide.deployedAt_of hshape.1

/-- **The source stage of solar-verify's Token**, for a function the check accepts: every call of
solar-verify's binding scope `stageScope fn [(2, 4096)]` (any argument words, no value, any storage
that writes slot 2) that SolidCore finishes, stage0 finishes the same way, under every oracle with
SolidCore's caller and hash of two words. -/
theorem stage (o : SolarTV.Machine.Oracle) (henv : SourceEnvOk o) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) {fn : Fn} (h : checkOn stage0 fn = some true) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c stage0
      (SolidCore.Verify.VC.stageScope fn [(2, 4096)]) := by
  obtain ⟨d, hd⟩ := deployed hc
  exact Generic.stageAtEnv o henv hd (check_of hc h)

/-- SolidCore type checks solar-verify's Token. -/
theorem contract_ok : ∃ c, contract? = .ok c := by
  have hshape := burnShape_eq
  unfold burnShape? at hshape
  split at hshape
  · next c hc => exact ⟨c, hc⟩
  · simp at hshape

/-- info: 'SolidCore.Refinement.Solar.VerifyTokenSource.check_transfer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_transfer_eq

/-- info: 'SolidCore.Refinement.Solar.VerifyTokenSource.stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stage

end SolidCore.Refinement.Solar.VerifyTokenSource


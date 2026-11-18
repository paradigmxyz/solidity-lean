import Verify.Generic.Expected
import Verify.Spec.HashScopeCheck
import Contracts.UniswapV2.ERC20.Slice.Post
import SolidCore.Solidity.Shared.PrecompileCrypto

/-!
# The gates of the 1200-byte any-caller binding, checked without the stage export

`Certified/erc20_any/Statement.lean` states the any-caller binding of UniswapV2ERC20.transfer over
the 1200 runtime bytes solar f71b7554 emits. It imports the generated stage export
(`uv2_erc20.gen.*`), which only the heavy run writes, so it cannot be elaborated here. Its gate
definitions need none of that export. Lines 143 to 215 of that file (`deployed` through
`specScoped`) are copied below byte for byte (the receipts diff them), and this module checks that
their premises are satisfiable and that the gates are not vacuous:

* sequential self-transfer: `seqStoreAt_self` (debit then credit of the same slot restores the
  storage) and `seq_self` (from `SeqPostAt` alone, with no hash premise, a self-transfer succeeds
  iff the balance covers the value and then leaves the storage as it was);
* overflow: `seq_self_no_overflow` (a self-transfer never fails the credit check), and
  `overflow_reachable`/`underflow_reachable` (both revert conditions are reachable at concrete
  addresses, by the kernel's Keccak-256);
* finite hash footprint: `footprint_eq` (exactly two preimages), `footprint_AB` and
  `footprint_AA` (`ScopedSep` holds at concrete callers, by the kernel's Keccak-256), and
  `footprint_model` (some hash function separates every finite footprint);
* satisfiable premises: `satisfiable` (the Statement's conjunct, for every real caller) and
  `scoped_inhabited` (a context and a valid call of `specScoped`, so `TargetPostAt`'s premise
  `ScopeAt` is met at a real call).

None of this proves `Expected`: that is the heavy run's `Proof.any` and `Proof.scopedExpected`.
-/

namespace Certified.erc20_any.Final

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey balanceSlot upd be32
  transferLog errorData addMsg subMsg)
open SolidCore.Verify.Generic (Source Spec Context Expected)
open SolidCore.Spec.TrustedBase (mappingPreimage)

/-- The storage the constructor writes: the domain separator at slot 3. -/
def deployed : List (Nat × Nat) :=
  [(3, 78390027508550153555773896992835392567232765649225488394068785439274740276969)]

/-- The declared entrypoint: calls whose selector is `transfer(address,uint256)`'s. -/
def entries : List (String × (Context → Call → Prop)) :=
  [("transfer(address,uint256)", fun _ call => EvmRules.Evm.shr 224 (calldataWord call 0) = 0xa9059cbb)]

/-- The statuses transfer may end with: success or one of SafeMath's reverts. -/
def Allowed (_call : Call) (obs : Observable) : Prop :=
  obs.success = true ∨ obs.output = errorData subMsg ∨ obs.output = errorData addMsg

def debitAt (a : Nat) (s : Nat → Nat) (v : Nat) : Nat → Nat := upd s (balKey a) (s (balKey a) - v)

def seqStoreAt (a : Nat) (s : Nat → Nat) (dst v : Nat) : Nat → Nat :=
  upd (debitAt a s v) (balKey dst) (debitAt a s v (balKey dst) + v)

/-- **What the source does** on `transfer(to, v)` sent by `a`: the debit, then the credit reading
the debited storage (so `a = to` is the sequential self-transfer), each checked for overflow. -/
def SeqPostAt (a : Nat) (call : Call) (obs : Observable) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    (obs.success = true ↔
      (v ≤ slotValue σ (balKey a) ∧ debitAt a (slotValue σ) v (balKey dst) + v < 2 ^ 256)) ∧
    (obs.success = true → obs.storage = seqStoreAt a (slotValue σ) dst v ∧
      obs.logs = [transferLog a dst v] ∧ obs.output = be32 1) ∧
    (obs.success = false → obs.storage = slotValue σ ∧ obs.logs = [] ∧
      obs.output = errorData (if v ≤ slotValue σ (balKey a) then addMsg else subMsg))

/-- **The finite hash footprint premise of a call sent by `a`**: Keccak-256 separated on the two
preimages of `a`'s and the recipient's balance slots, and nothing else. -/
def ScopeAt (a : Nat) (call : Call) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    ScopedSep (transferFootprint balanceSlot a dst)

/-- **The caller-aware transfer property.** -/
def TargetPostAt (a : Nat) (call : Call) (obs : Observable) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    (a ≠ dst →
      (obs.success = true ↔
        v ≤ slotValue σ (balKey a) ∧ slotValue σ (balKey dst) + v < 2 ^ 256) ∧
      (obs.success = true → obs.storage (balKey a) = slotValue σ (balKey a) - v ∧
        obs.storage (balKey dst) = slotValue σ (balKey dst) + v)) ∧
    (a = dst →
      (obs.success = true ↔ v ≤ slotValue σ (balKey a)) ∧
      (obs.success = true → obs.storage = slotValue σ)) ∧
    (obs.success = true → obs.logs = [transferLog a dst v] ∧ obs.output = be32 1 ∧
      ∀ n, n % 2 ^ 256 ≠ balKey a → n % 2 ^ 256 ≠ balKey dst → obs.storage n = slotValue σ n) ∧
    (obs.success = false → obs.storage = slotValue σ ∧ obs.logs = [] ∧
      obs.output = errorData (if v ≤ slotValue σ (balKey a) then addMsg else subMsg))

def PostAt (a : Nat) (call : Call) (obs : Observable) : Prop :=
  SeqPostAt a call obs ∧ (ScopeAt a call → TargetPostAt a call obs)

/-- Every real caller, no hash premise in the contexts or the valid calls. -/
def specAny : Spec where
  Contexts ctx := ctx.Ok
  entries := entries
  Valid _ := Valid deployed
  Allowed _ := Allowed
  Post ctx := PostAt ctx.caller
  gas _ _ := 8199112
  assumptions := []

/-- Every real caller whose own footprint is separated; each valid call carries its footprint. -/
def specScoped : Spec where
  Contexts ctx := ctx.Ok ∧ ScopedSep (transferFootprint balanceSlot ctx.caller ctx.caller)
  entries := entries
  Valid ctx call := Valid deployed call ∧ ScopeAt ctx.caller call
  Allowed _ := Allowed
  Post ctx := TargetPostAt ctx.caller
  gas _ _ := 8199112
  assumptions := []


end Certified.erc20_any.Final

namespace Certified.erc20_any.Gates

open SolarTV SolidCore.Refinement SolidCore.Spec
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey balanceSlot upd slotValue_mod
  balKey_mod)
open SolidCore.Verify.Generic (Context)
open SolidCore.Spec.TrustedBase (mappingPreimage)
open Certified.erc20_any.Final

theorem slot_lt (σ : List (Nat × Nat)) (k : Nat) : slotValue σ k < 2 ^ 256 :=
  Generic.slotValue_lt σ k

theorem debitAt_self (a v : Nat) (σ : List (Nat × Nat)) :
    debitAt a (slotValue σ) v (balKey a) = slotValue σ (balKey a) - v := by
  simp only [debitAt, upd, balKey_mod, ite_true]

/-- **Sequential self-transfer**: the debit, then the credit reading the debited slot, leaves the
storage as it was. -/
theorem seqStoreAt_self (a v : Nat) (σ : List (Nat × Nat)) (hv : v ≤ slotValue σ (balKey a)) :
    seqStoreAt a (slotValue σ) a v = slotValue σ := by
  funext n
  rw [seqStoreAt, debitAt_self]
  by_cases h : n % 2 ^ 256 = balKey a
  · simp only [upd, h, ite_true]
    rw [← UniswapV2.ERC20.Slice.slotValue_mod σ n, h]
    omega
  · simp only [upd, debitAt, h, ite_false]

/-- **Overflow, self case**: a self-transfer never fails the credit's overflow check. -/
theorem seq_self_no_overflow (a v : Nat) (σ : List (Nat × Nat)) :
    (v ≤ slotValue σ (balKey a) ∧ debitAt a (slotValue σ) v (balKey a) + v < 2 ^ 256) ↔
      v ≤ slotValue σ (balKey a) := by
  rw [debitAt_self]
  have := slot_lt σ (balKey a)
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by omega⟩

/-- **The self-transfer decided from `SeqPostAt` alone**, with no hash premise. -/
theorem seq_self {a : Nat} {call : Call} {obs : Observable} (h : SeqPostAt a call obs)
    (σ : List (Nat × Nat)) (v : Nat) (hc : call = transferCall σ a v) (ha : a < 2 ^ 160)
    (hv : v < 2 ^ 256) :
    (obs.success = true ↔ v ≤ slotValue σ (balKey a)) ∧
      (obs.success = true → obs.storage = slotValue σ) := by
  obtain ⟨hs, hok, -⟩ := h σ a v hc ha hv
  have hiff : obs.success = true ↔ v ≤ slotValue σ (balKey a) :=
    hs.trans (seq_self_no_overflow a v σ)
  refine ⟨hiff, fun ht => ?_⟩
  rw [(hok ht).1]
  exact seqStoreAt_self a v σ (hiff.1 ht)

/-- A caller (`HashScopeCheck.addrA`). -/
abbrev addrA : Nat := 0x5B38Da6a701c568545dCfcB03FcB875f56beddC4
/-- A recipient (`HashScopeCheck.addrB`). -/
abbrev addrB : Nat := 0xAb8483F64d9C6d1EcF9b849Ae677dD3315835cb2

set_option maxRecDepth 100000 in
/-- **The credit's overflow is reachable**: `addrA` holds 1, `addrB` holds `2 ^ 256 - 1`; sending 1
passes the debit and fails the credit. -/
theorem overflow_reachable :
    ∃ σ : List (Nat × Nat), 1 ≤ slotValue σ (balKey addrA) ∧
      ¬ debitAt addrA (slotValue σ) 1 (balKey addrB) + 1 < 2 ^ 256 :=
  ⟨[(balKey addrA, 1), (balKey addrB, 2 ^ 256 - 1)], by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- **The debit's underflow is reachable**: `addrA` holds 0 and sends 1. -/
theorem underflow_reachable :
    ∃ σ : List (Nat × Nat), ¬ 1 ≤ slotValue σ (balKey addrA) :=
  ⟨[(balKey addrA, 0)], by decide +kernel⟩

/-- **The finite hash footprint**: exactly the caller's and the recipient's balance preimages. -/
theorem footprint_eq (a dst : Nat) :
    transferFootprint balanceSlot a dst = [mappingPreimage a balanceSlot, mappingPreimage dst balanceSlot] :=
  rfl

/-- **The footprint premise holds at concrete distinct addresses**, by the kernel's Keccak-256. -/
theorem footprint_AB : ScopedSep (transferFootprint balanceSlot addrA addrB) :=
  SolidCore.Spec.real_transfer_AB

/-- **The footprint premise holds for a self-transfer**, by the kernel's Keccak-256. -/
theorem footprint_AA : ScopedSep (transferFootprint balanceSlot addrA addrA) :=
  SolidCore.Spec.real_transfer_AA

/-- **Some hash function separates every finite footprint**: the premise is never `False` in
disguise. -/
theorem footprint_model (a dst : Nat) : ∃ h, SeparatedBy h (transferFootprint balanceSlot a dst) :=
  exists_separatedBy _

theorem covers_deployed : Generic.Covers deployed deployed :=
  fun kv hkv => ⟨kv, hkv, rfl⟩

/-- **Satisfiable for every real caller**: the Statement's conjunct, the transfer of 0 to itself. -/
theorem satisfiable : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∃ call, specAny.Valid ⟨a⟩ call :=
  fun a ha _ => ⟨transferCall deployed a 0, deployed, a, 0, covers_deployed, ha, by decide, rfl⟩

theorem transferCall_inj {σ σ' : List (Nat × Nat)} {dst dst' v v' : Nat} (hto : dst < 2 ^ 256)
    (hv : v < 2 ^ 256) (hto' : dst' < 2 ^ 256) (hv' : v' < 2 ^ 256)
    (h : transferCall σ dst v = transferCall σ' dst' v') : dst = dst' := by
  have ha := congrArg callArgs h
  simp only [callArgs, transferCall] at ha
  rw [words_calldata _ (by simp; omega), words_calldata _ (by simp; omega)] at ha
  simp only [List.cons.injEq] at ha
  exact ha.1

/-- **`specScoped` is inhabited at a real caller**: `addrA`'s context, and the transfer of 0 to
`addrB` as a valid call whose `ScopeAt` premise holds, so `TargetPostAt` is required there. -/
theorem scoped_inhabited :
    specScoped.Contexts ⟨addrA⟩ ∧ specScoped.Valid ⟨addrA⟩ (transferCall deployed addrB 0) := by
  refine ⟨⟨⟨by decide, by decide⟩, footprint_AA⟩,
    ⟨⟨deployed, addrB, 0, covers_deployed, by decide, by decide, rfl⟩, ?_⟩⟩
  intro σ dst v hc hdst hv
  obtain rfl := transferCall_inj (by decide) (by decide) (by omega) hv hc
  exact footprint_AB

end Certified.erc20_any.Gates

#print axioms Certified.erc20_any.Gates.seqStoreAt_self
#print axioms Certified.erc20_any.Gates.seq_self
#print axioms Certified.erc20_any.Gates.seq_self_no_overflow
#print axioms Certified.erc20_any.Gates.overflow_reachable
#print axioms Certified.erc20_any.Gates.underflow_reachable
#print axioms Certified.erc20_any.Gates.footprint_AB
#print axioms Certified.erc20_any.Gates.footprint_AA
#print axioms Certified.erc20_any.Gates.footprint_model
#print axioms Certified.erc20_any.Gates.satisfiable
#print axioms Certified.erc20_any.Gates.scoped_inhabited

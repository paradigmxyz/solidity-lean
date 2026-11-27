import Verify.Phase3.RecSum.Proofs.Stages
import Verify.Phase3.RecSum.Spec

/-! # RecSum: the recursive function's property on the final EVM IR

`recsum_certified` (Proofs/Stages.lean) chains the eight backend stages of `RecSum` from the first
lowered MIR to the final EVM IR, each proved through cut points at the recursive function's entry
and resume points (tools/certify/rec_cuts.py), on every call. `total_returns` (Spec.lean) proves
`total(n)` returns `n * (n + 1) / 2` on the lowered MIR by induction on the recursion's measure.
Together: the final EVM IR returns the same bytes, with the same storage, transient storage and
world (`Agree`). What this does not reach: the bytecode (the assembly checker `checkL` needs
static stack heights per block, which a recursive call does not have) and the Solidity source
(the generic driver's source stage). -/

namespace SolarTV.Milestone.RecSum

open Machine SolarTV.Export.RecSum

/-- **`total(n)` on the final EVM IR**: on a call with no value, `total`'s selector, a full
argument word and `n ≤ 64`, the final EVM IR ends, returning the 32 bytes of `n * (n + 1) / 2`
with the storage, transient storage and world the lowered MIR ends with. -/
theorem total_returns_evmir (o : Oracle) (call : Call)
    (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 2971266046)
    (hsz : ¬ BitVec.ofNat 256 call.calldata.size < 36)
    (hn : (calldataWord call 4).toNat ≤ 64) :
    ∃ r', EVM.Program.layer.Ends o evm6 call r' ∧ Agree (returned call (calldataWord call 4).toNat) r' :=
  recsum_certified o call trivial _ (total_returns o call hv hsel hsz hn)

/-- The premises are met: `total(10)` with no value. -/
def call10 : Call :=
  { calldata := ⟨#[0xb1, 0x19, 0xeb, 0xfe] ++ (List.replicate 31 (0 : UInt8)).toArray ++ #[10]⟩,
    callvalue := 0, storage := [] }

theorem call10_returns (o : Oracle) :
    ∃ r', EVM.Program.layer.Ends o evm6 call10 r' ∧ Agree (returned call10 10) r' := by
  have h4 : (calldataWord call10 4).toNat = 10 := by decide +kernel
  have := total_returns_evmir o call10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [h4]; decide)
  rwa [h4] at this

theorem tri_10 : tri 10 = 55 := by decide

/-- info: 'SolarTV.Milestone.RecSum.total_returns_evmir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms total_returns_evmir

/-- info: 'SolarTV.Milestone.RecSum.call10_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms call10_returns

end SolarTV.Milestone.RecSum

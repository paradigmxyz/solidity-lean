import Contracts.VerifyCounter.BumpTotal
import verify_counter.Proofs.Stages

/-!
# bump: a block bound on the final EVM IR from the loop's rank

Every stage from the first lowered MIR to the final EVM IR states its target segments' fuel
(`<stage>_bounded : CutPoint.BoundedSim … K'`, written by the certify driver). Chained
(`CutPoint.BoundedSim.trans`), the stages match the MIR's segments one for one with segments of
`evm11` of at most 22 blocks each. The MIR's ranking certificate for bump's loop (`n - i`, the
inferred measure, `Bump.wseg0`, `Bump.wseg`) then bounds the run of the final EVM IR
(`CutPoint.ends_within_sim_start`): every call of bump ends on `evm11` within `(n + 2) * 22`
blocks. This is the block count a gas bound on the bytecode multiplies by the most a block
costs; it is a step bound derived from the rank, not a chosen fuel.
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1 SolarTV.Milestone.VerifyCounter

theorem evm11_ends_within (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ r, Machine.iterate (EVM.Program.block o call evm11)
      (((calldataWord call 4).toNat + 2) * 22) (0, [], State.initial call) = some r := by
  have chain := ((((((((((((mir1_bounded o call).trans (sched_bounded o call)).trans
    (evm1_bounded o call)).trans (evm2_bounded o call)).trans (evm3_bounded o call)).trans
    (evm4_bounded o call)).trans (evm5_bounded o call)).trans (evm6_bounded o call)).trans
    (evm7_bounded o call)).trans (evm8_bounded o call)).trans (evm9_bounded o call)).trans
    (evm10_bounded o call)).trans (evm11_bounded o call)
  obtain ⟨r, ran, -⟩ := CutPoint.ends_within_sim_start (sim := chain) (Inferred.rank call) 40 22
    (calldataWord call 4).toNat (rank_le call) (x₀ := start call)
    (x₀' := ((0, [], State.initial call) : Nat × EVM.Stack × State))
    (start := wseg0 o call hsel) (segment := wseg o call)
    (rel := by
      repeat' (first | exact ⟨_, List.Mem.head _, rfl, rfl⟩ | (apply Exists.intro; apply And.intro)))
  exact ⟨r, by rw [CutPoint.iterate_eq]; exact ran⟩

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.evm11_ends_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evm11_ends_within

end SolarTV.Milestone.VerifyCounter.Bump

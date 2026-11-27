import Verify.Phase3.RecSum.Proofs.Execution
import Verify.Phase3.RecSum.Spec

/-! # RecSum: the recursive function's property on the exact bytecode

`recsum_bytecode_of_mir` (Proofs/Execution.lean, generated) carries every end of the first lowered MIR to
the bytecode solar emits for RecSum.sol: the backend stages through the recursive function's cut points
(Proofs/Stages.lean), then the assembly checker with frames (`AssembleRec.checkF`), whose dynamic jumps
return through the frames the call sites push and whose cut points' heights come from the last stage's
relation. `total_returns` (Spec.lean) proves `total(n)` returns `n * (n + 1) / 2` on the lowered MIR by
induction on the recursion's measure. Together: the bytecode returns it, at a gas from the checker's
bound for the run's blocks. What this does not reach: the Solidity source (the generic driver's source
stage), so the MIR's behaviour is the specification here, not the source's. -/

namespace SolarTV.Milestone.RecSum

open Machine SolarTV.Export.RecSum

/-- An oracle to run the stages under: RecSum's bytecode reads nothing an oracle answers (its
certificate reads neither CALLER, hashes nor the environment). -/
def oracle0 : Oracle := ⟨fun _ _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩

/-- **`total(n)` on the exact bytecode**: on a call with no value, `total`'s selector, a full argument
word and `n ≤ 64`, from some gas on the runtime bytecode solar emits for RecSum.sol succeeds, returning
the 32 bytes of `n * (n + 1) / 2`. -/
theorem total_returns_bytecode (call : Call)
    (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 2971266046)
    (hsz : ¬ BitVec.ofNat 256 call.calldata.size < 36)
    (hn : (calldataWord call 4).toNat ≤ 64) :
    ∃ G, ∀ gas, G ≤ gas → ∃ obs,
      SolidCore.Refinement.Final.Target.runWith gas code call = some obs ∧ obs.success = true ∧
      obs.output = (Mem.wordBytes (BitVec.ofNat 256 (tri (calldataWord call 4).toNat))).map
        BitVec.toNat := by
  obtain ⟨r', n, hag, hrun⟩ := recsum_bytecode_of_mir oracle0 (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) call _ (total_returns oracle0 call hv hsel hsz hn)
  refine ⟨SolidCore.Refinement.Solar.AssembleLoop.gasBoundL cert n, fun gas hg =>
    ⟨_, hrun gas hg, ?_⟩⟩
  obtain ⟨h', s'⟩ := r'
  cases h' with
  | ret e =>
    simp only [Agree] at hag
    obtain ⟨rfl, -⟩ := hag
    simp [observe]
  | stop =>
    simp only [Agree] at hag
    exact absurd hag.1 (by simp [Mem.wordBytes])
  | revert e => simp [Agree] at hag
  | invalid => simp [Agree] at hag

open SolidCore.Refinement.Solar.AssembleRec in
set_option maxRecDepth 100000 in
/-- The frames are what the check rests on: with none, a return in the function reaches the caller's
words untyped, and the checker refuses the bytecode. -/
example : checkFS evm6 code cert maxs heads { blocks := [], calls := [] } = false := by
  decide +kernel

open SolidCore.Refinement.Solar.AssembleRec in
set_option maxRecDepth 100000 in
/-- With the recursive call's kept words claimed as data, the caller's return label is lost where it
resumes, and the checker refuses the bytecode too. -/
example : checkFS evm6 code cert maxs heads
    { blocks := [1, 4, 5], calls := [(3, [some false], none), (4, [some false, some false], some 0)] } =
      false := by
  decide +kernel


/-- info: 'SolarTV.Milestone.RecSum.total_returns_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms total_returns_bytecode

end SolarTV.Milestone.RecSum


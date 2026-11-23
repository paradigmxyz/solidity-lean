import Verify.LoopSource.MirLink.Statement

/-!
# Counter.bump's calls under an iteration bound

\`BumpCallBounded K\`: a call of \`bump(a)\` with \`a ≤ K\` (so its loop runs at most \`K\` times), any
storage and no value. It is the valid-call set under which \`Shapes.Resources\` is to be stated;
\`bounded_inhabited\` shows it is inhabited for every \`K\`, by \`bump(0)\`, and \`bounded_sub\` that it
is a subset of \`BumpCall\`. **Resources itself is not proved here: it stays OPEN.**
-/

namespace Verify.LoopSource.Equiv.CounterGas
open SolidCore.Refinement Contracts.VerifyCounter.Source Verify.LoopSource.MirLink

/-- **The iteration-bound premise**: \`bump(a)\` with \`a ≤ K\`. -/
def BumpCallBounded (K : Nat) (call : Call) : Prop :=
  ∃ σ a, a ≤ K ∧ a < 2 ^ 256 ∧ call = bumpCall σ a

/-- **Its inhabitation witness**: \`bump(0)\` from empty storage, for every bound. -/
theorem bounded_inhabited (K : Nat) : ∃ call, BumpCallBounded K call :=
  ⟨bumpCall [] 0, [], 0, Nat.zero_le K, Nat.two_pow_pos 256, rfl⟩

/-- Every bounded call is a valid call of \`bump\`. -/
theorem bounded_sub {K : Nat} {call : Call} (h : BumpCallBounded K call) : BumpCall call := by
  obtain ⟨σ, a, -, ha, rfl⟩ := h
  exact ⟨σ, a, ha, rfl⟩

end Verify.LoopSource.Equiv.CounterGas

/-- info: 'Verify.LoopSource.Equiv.CounterGas.bounded_inhabited' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterGas.bounded_inhabited

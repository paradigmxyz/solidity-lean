import Verify.LoopSource.Equiv.CounterSame
import Verify.LoopSource.Equiv.CounterDeploy5
import Verify.LoopSource.Equiv.CounterDeploy8

/-!
# Counter's expected theorem with its creation discharged (box-built)

\`counter_expected_closed\`: for the pinned \`[n]\`, \`n ∈ {5, 8}\`, and \`K ≤ Kmax\`:

* \`Expected (src n) (spec n K) bytecode\` (\`counter_expected\`), and
* the lifecycle statement at the expected theorem's own \`(c, fuel)\`: solar's init code with \`[n]\`
  deploys \`runtimeCode bytecode\` leaving \`[(1, n)]\` (EthLib's creation, \`CounterDeploy{n}\`), and
  SolidCore's constructor on \`[n]\` leaves \`[(1, n)]\` (\`CounterSame.source_half\`), whose state is the
  one the expected theorem runs against (\`CounterSame.same_d\`).

No lifecycle premise is taken. Scope premises stay in \`spec.Valid\`: \`BumpCallBounded K\`, call value
0, and the **per-call storage load cover**, which is Expected's call model (a call carries its own
storage; \`Verify/Generic/Expected.lean:120–150\`), not the deployed account storage.
-/

namespace Verify.LoopSource.Equiv.CounterClosedCtx
open SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source
open SolidCore.Verify.Generic

theorem deploys {n : Nat} (hn : n = 5 ∨ n = 8) :
    Deploys (Verify.Lifecycle.initArgs Verify.LoopSource.Equiv.CounterCtor.counterInit [n])
      (runtimeCode SolarTV.Export.Counter.bytecode) [(1, n)] := by
  rw [Verify.LoopSource.Equiv.CounterSame.code_eq]
  rcases hn with rfl | rfl
  · exact Verify.LoopSource.Equiv.CounterDeploy5.deploys
  · exact Verify.LoopSource.Equiv.CounterDeploy8.deploys

/-- **Counter, expected theorem and lifecycle statement**, with no lifecycle premise. -/
theorem counter_expected_closed {n : Nat} (hn : n = 5 ∨ n = 8) {K : Nat} (hK : K ≤ Verify.LoopSource.Equiv.CounterCtx.Kmax) :
    Expected (Verify.LoopSource.Equiv.CounterCtx.src n) (Verify.LoopSource.Equiv.CounterCtx.spec n K) SolarTV.Export.Counter.bytecode ∧
      ∃ c, contract? = .ok c ∧
        Verify.Lifecycle.Statement fuel c Verify.LoopSource.Equiv.CounterCtor.counterInit
          (runtimeCode SolarTV.Export.Counter.bytecode) [n] [(1, n)] ∧
        ∀ d d', Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d [(1, n)] →
          LoadDeployed fuel c [n] d' → d = d' := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨(Verify.LoopSource.Equiv.CounterCtx.counter_expected hn hK).1, c, hc,
    ⟨deploys hn, Verify.LoopSource.Equiv.CounterSame.source_half hc hn⟩, fun _ _ => Verify.LoopSource.Equiv.CounterSame.same_d⟩

end Verify.LoopSource.Equiv.CounterClosedCtx

/-- info: 'Verify.LoopSource.Equiv.CounterClosedCtx.counter_expected_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterClosedCtx.counter_expected_closed

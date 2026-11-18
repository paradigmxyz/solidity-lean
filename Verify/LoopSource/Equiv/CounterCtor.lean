import Verify.LoopSource.Equiv.CtorBridge
import Verify.Lifecycle.KernelIndex
import Verify.LoopSource.MirLink.Link
import Verify.LoopSource.Proof.LoopVC

/-!
# Counter's deployment with constructor arguments: gates for the bridge

Counter's constructor is \`constructor(uint256 _limit)\`. The kernel checks, on copies of the type
checker that read the selectors from Counter's \`selectorTable\` (\`using selector_eq\`), what
SolidCore's constructor does with each argument list (\`gates_eq\`):

* \`[8]\` and \`[5]\` deploy with storage \`[(1, 8)]\` and \`[(1, 5)]\` and no logs (two constructor values);
* \`[8]\` does not deploy with storage \`[(1, 9)]\` (a wrong storage claim is refused);
* \`[]\` and \`[8, 9]\` do not construct at all (missing or extra words): no run, as before arguments.

\`counter_semAt_eq_runtime\`: for \`n ∈ {5, 8}\`, on every call of \`bump(a)\` whose storage writes slot 1,
Counter deployed with \`[n]\` runs in \`Context.default\` exactly as its runtime code does
(\`semAt_eq_runtime\`), at the statement's fuel. \`before_fails\`: deployed with no words it has no
run on any call (the gap \`solidCoreFrom\` left). Fixed-context evidence only; Counter stays outside
the accepted subset.
-/

namespace Verify.LoopSource.Equiv.CounterCtor
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source

/-- What SolidCore's constructor does with each argument list, on Counter. -/
def gates? : Option (List Bool) :=
  match contract? with
  | .ok c => some
      [Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 8)],
       Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [5]) [(1, 5)],
       Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 9)],
       (match SolidCore.Refinement.Source.deployArgs? fuel [] c with | some (CallResult.returned _ _) => true | _ => false),
       (match SolidCore.Refinement.Source.deployArgs? fuel [8, 9] c with | some (CallResult.returned _ _) => true | _ => false)]
  | .error _ => none

kernel_rfl gates_eq gates? (some [true, true, false, false, false]) using selector_eq Verify.Lifecycle.mkIdx_eq

theorem gate {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    gates? = some [Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 8)],
       Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [5]) [(1, 5)],
       Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 9)],
       (match SolidCore.Refinement.Source.deployArgs? fuel [] c with | some (CallResult.returned _ _) => true | _ => false),
       (match SolidCore.Refinement.Source.deployArgs? fuel [8, 9] c with | some (CallResult.returned _ _) => true | _ => false)] := by
  unfold gates?; rw [hc]

theorem gates_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 8)] = true ∧
    Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [5]) [(1, 5)] = true ∧
    Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 9)] = false ∧
    (match SolidCore.Refinement.Source.deployArgs? fuel [] c with | some (CallResult.returned _ _) => true | _ => false) = false ∧
    (match SolidCore.Refinement.Source.deployArgs? fuel [8, 9] c with | some (CallResult.returned _ _) => true | _ => false) = false := by
  have h := gates_eq
  rw [gate hc] at h
  simp only [Option.some.injEq, List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- **Before**: deployed with no words, Counter has no run on any call. -/
theorem before_fails {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (caller : Nat) (call : Call) :
    SolidCore.Refinement.Source.runFromArgs caller fuel [] c call = none := by
  apply runFromArgs_eq_none
  intro d vs h
  have := (gates_of hc).2.2.2.1
  rw [h] at this
  simp at this

/-- **After**: deployed with \`[n]\`, \`n ∈ {5, 8}\`, Counter runs every \`bump(a)\` whose storage writes
slot 1 in \`Context.default\` as its runtime code does. -/
theorem counter_semAt_eq_runtime {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n = 5 ∨ n = 8) {call : Call}
    (hv : SelCallCov bumpSel bumpFn [256] [(1, n)] call) :
    (solidCoreFromArgs callerAddress fuel [n]).run c call = (solidCoreRuntime fuel).run c call := by
  have hlife : Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) [(1, n)] = true := by
    rcases hn with rfl | rfl
    · exact (gates_of hc).2.1
    · exact (gates_of hc).1
  obtain ⟨d, hd⟩ := Verify.Lifecycle.deployedAtWith_of hlife
  obtain ⟨T, hT⟩ := tree_ok
  exact semAt_eq_runtime hd (by decide) (shape_of hc).2.2 rfl rfl
    (Verify.LoopSource.MirLink.bodyRuns_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc hc) hT hv

end Verify.LoopSource.Equiv.CounterCtor

/-- info: 'Verify.LoopSource.Equiv.CounterCtor.counter_semAt_eq_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterCtor.counter_semAt_eq_runtime

/-- info: 'Verify.LoopSource.Equiv.CounterCtor.before_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterCtor.before_fails

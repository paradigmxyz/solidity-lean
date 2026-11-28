import Verify.LoopSource.Equiv.CtorBridge
import Verify.Lifecycle.KernelIndex
import Verify.Lifecycle.Deploy.Ctors
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

theorem gates_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 8)] = true ∧
    Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [5]) [(1, 5)] = true ∧
    Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [8]) [(1, 9)] = false ∧
    (match SolidCore.Refinement.Source.deployArgs? fuel [] c with | some (CallResult.returned _ _) => true | _ => false) = false ∧
    (match SolidCore.Refinement.Source.deployArgs? fuel [8, 9] c with | some (CallResult.returned _ _) => true | _ => false) = false := by
  have h := gates_eq
  unfold gates? at h
  rw [hc] at h
  simpa only [Option.some.injEq, List.cons.injEq, and_true] using h

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
    (hv : SelCallCov bumpSel bumpFn [2 ^ 256 - 1] [(1, n)] call) :
    (solidCoreFromArgs callerAddress fuel [n]).run c call = (solidCoreRuntime fuel).run c call := by
  have hlife : Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) [(1, n)] = true := by
    rcases hn with rfl | rfl
    · exact (gates_of hc).2.1
    · exact (gates_of hc).1
  obtain ⟨d, hd⟩ := Verify.Lifecycle.deployedAtWith_of hlife
  obtain ⟨T, hT⟩ := tree_ok
  exact semAt_eq_runtime hd (by decide) (shape_of hc).2.2 rfl rfl
    (Verify.LoopSource.MirLink.bodyRuns_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc hc) hT hv

/-! ## Typed admission of Counter's creation code -/

/-- solar's init code for Counter (307 bytes, the lane's lifecycle receipt; sha256 4be2987c…). -/
def counterInit : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat 8095097942374910459758325860891084340365005107621154363759676945331737934686436138519866698795250427326168791466014031795999049982978037003157598373462669307061139024541306293506332738965612022261660496287689080251198250264128488077029329134040459017511628455929907115049986884887339390678688120925175384060179577863909654564543519318962158535026970506712094155005087922452985155631999008973209960331655241728821170709670561660147788478578470044113734854142083790491327015233121954059906117758350139013168330834049275537595104880492331530802881305688671260885174942033106912517793068528945866397923883763588643483110251402049097329194978482385377126470529596145138337867697673784597343186858607892529775107615288656891123824618404180925693 307

/-- Admission on a pinned word list. -/
def admit? (ws : List Nat) (creation : ByteArray) : Option (Except CtorBlocked Unit) :=
  match contract? with
  | .ok c => some (admitCtor? c counterInit creation ws)
  | .error _ => none

/-- Admitted: \`[8]\`, \`[5]\`. Refused: wrong words for the creation code, missing and extra words. -/
def admits? : List Bool :=
  [(match admit? [8] (Verify.Lifecycle.initArgs counterInit [8]) with | some (.ok ()) => true | _ => false),
   (match admit? [5] (Verify.Lifecycle.initArgs counterInit [5]) with | some (.ok ()) => true | _ => false),
   (match admit? [9] (Verify.Lifecycle.initArgs counterInit [8]) with | some (.error .suffix) => true | _ => false),
   (match admit? [] (Verify.Lifecycle.initArgs counterInit []) with | some (.error (.arity 1 0)) => true | _ => false),
   (match admit? [8, 9] (Verify.Lifecycle.initArgs counterInit [8, 9]) with | some (.error (.arity 1 2)) => true | _ => false)]

kernel_rfl admits_eq admits? [true, true, true, true, true] using selector_eq Verify.Lifecycle.mkIdx_eq

theorem admit_ok {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n = 5 ∨ n = 8) :
    admitCtor? c counterInit (Verify.Lifecycle.initArgs counterInit [n]) [n] = .ok () := by
  have h := admits_eq
  unfold admits? admit? at h
  rw [hc] at h
  simp only [List.cons.injEq] at h
  obtain ⟨h8, h5, -⟩ := h
  rcases hn with rfl | rfl
  · revert h5; split <;> simp_all
  · revert h8; split <;> simp_all

/-- **Counter's admission**: \`CtorAdmits\` on \`[n]\`, \`n ∈ {5, 8}\`, by \`admitCtor?_sound\`. -/
theorem counter_admits {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n = 5 ∨ n = 8) :
    CtorAdmits c counterInit (Verify.Lifecycle.initArgs counterInit [n]) [n] :=
  admitCtor?_sound (admit_ok hc hn)

end Verify.LoopSource.Equiv.CounterCtor

/-- info: 'Verify.LoopSource.Equiv.CounterCtor.counter_semAt_eq_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterCtor.counter_semAt_eq_runtime

/-- info: 'Verify.LoopSource.Equiv.CounterCtor.before_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterCtor.before_fails

/-- info: 'Verify.LoopSource.Equiv.CounterCtor.counter_admits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterCtor.counter_admits


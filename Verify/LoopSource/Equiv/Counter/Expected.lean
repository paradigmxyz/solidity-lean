import Verify.LoopSource.Equiv.Counter.Obl
import Verify.LoopSource.Equiv.Stage
import Verify.LoopSource.MirLink.Link
import Verify.LoopSource.Proof.LoopVC

/-!
# Counter.bump at the driver's expected type

* \`counter_stage\`: \`Counter.bump\`'s source semantics (\`solidCoreRuntime\` at the statement's fuel) is
  compiled to its lowered MIR (\`SolarTV.Export.Counter.stage0\`, exported by the base compiler)
  without changing a result, on every valid call \`bump(a)\`, under every oracle the source allows.
  Its premises are all discharged: the source loop's run (\`body_runs_vc\`), the cut-point check
  (\`CounterObl.leaves\`) and the loop's obligations (\`CounterObl.obl\`).
* \`counter_equiv\`: \`Shapes.Equiv\` for the runtime bytes \`code\`, **given** the backend's MIR-to-EVM-IR
  stage for that MIR and the assembler's loop check of \`code\`. Those two are premises, not proved
  here.
* \`counter_certified\`: the driver's whole \`Shapes.Certified\` statement with \`bump\`'s postcondition,
  **given** those two and \`Shapes.Resources\` for \`code\` (the gas bound), also a premise.

The valid calls are every \`bump(a)\` with \`a < 2 ^ 256\`, any storage and no value: a precondition
every ABI-encoded call meets.
-/

namespace Verify.LoopSource.Equiv.CounterExpected
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar SolidCore.Solidity.Source
open Contracts.VerifyCounter.Source Verify.LoopSource.Generic Verify.LoopSource.Equiv
open Verify.LoopSource.MirLink

/-- **Counter's source-to-MIR stage**, with no assumed premise. -/
theorem counter_stage {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (o : Oracle) (ho : SourceAsk .off o) :
    Stage (solidCoreRuntime Contracts.VerifyCounter.Source.fuel) (mirSem o) c
      SolarTV.Export.Counter.stage0 BumpCall := by
  rw [← bump_valid]
  exact loop_stage (by decide) (shape_of hc).2.2 rfl rfl
    (bodyRuns_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc hc) CounterObl.tree
    CounterObl.leaves CounterObl.obl (fun _ _ _ => trivial) o ho

/-- **\`Shapes.Equiv\` for Counter**, given the backend stage and the assembler's loop check. -/
theorem counter_equiv {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat}
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) SolarTV.Export.Counter.stage0 q scope)
    (hscope : ∀ call, BumpCall call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true) :
    Shapes.Equiv stmtSem c code BumpCall := by
  rw [← bump_valid]
  exact loop_equiv (by decide) (shape_of hc).2.2 rfl rfl
    (bodyRuns_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc hc) CounterObl.tree
    CounterObl.leaves CounterObl.obl (fun _ _ _ => trivial) backend
    (fun call h => hscope call (bump_valid ▸ h)) asm

/-- **The driver's Statement for Counter**, given the backend stage, the assembler's loop check and
the bytes' resources. -/
theorem counter_certified {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop}
    {cert : Assemble.Cert} {mx : List Nat} (G : Call → Nat)
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) SolarTV.Export.Counter.stage0 q scope)
    (hscope : ∀ call, BumpCall call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hres : ∀ c, contract? = .ok c → Shapes.Resources stmtSem c code BumpCall G) :
    ∃ c, contract? = .ok c ∧ Shapes.Certified stmtSem c code BumpCall (fun _ _ => True) BumpPost G :=
  statement_link Contracts.VerifyCounter.LoopVC.body_runs_vc code _ _ G (fun _ _ _ _ _ => trivial)
    tree_post (fun c hc => counter_equiv hc backend hscope asm) hres

end Verify.LoopSource.Equiv.CounterExpected

/-- info: 'Verify.LoopSource.Equiv.CounterExpected.counter_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExpected.counter_stage

/-- info: 'Verify.LoopSource.Equiv.CounterExpected.counter_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExpected.counter_equiv

/-- info: 'Verify.LoopSource.Equiv.CounterExpected.counter_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExpected.counter_certified

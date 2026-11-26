import Verify.LoopSource.Equiv.EraseLoopStage
import Verify.Gas.FixedFuel.Gas

/-!
# Resources from the source, for a function with a counted loop

\`Verify.Gas.FixedFuel.resources_of_verdict\` gives \`Shapes.Resources\` of any semantics that is
total on the valid calls and has a stage to the final EVM IR. The driver's loop-resources run
proves it with the final EVM IR as the source (the stage to itself). Here the source is
SolidCore's runtime: the stage is the loop's source edge from the erasure
(\`source_edge_of_eraseLoop\`), and totality comes from the erasure too, so a function whose body
\`eraseLoopStmt\` erases (a counted \`for\` loop, \`EraseLoop.lean\`) gets resources from the source
with no hand-written body summary.

* \`loop_resources_of_eraseLoop\`: \`Shapes.Resources (solidCoreRuntime fuel) c code Valid\` on any
  \`Valid\` inside the function's valid calls, from the erasure, the cut certificate and its
  obligations, the backend's stage, the loop checker, the loop facts of the final EVM IR and a
  bounded verdict.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar

/-- **Resources from the source, for a function whose body \`eraseLoopStmt\` erases.**

The loop's source edge (\`source_edge_of_eraseLoop\`: the source-to-MIR stage composed with the
backend's MIR-to-EVM-IR stage), narrowed to \`Valid\`, is the stage \`resources_of_verdict\` takes;
the source is total on \`Valid\` because every valid call runs to the erased tree's observable
(\`runs_of_bodyRuns\` with \`bodyRuns_of_eraseLoop\`). With the loop checker on the bytes, the
fixed-fuel loop facts of the final EVM IR and a bounded verdict, the bytecode gives the source's
result from \`G\` gas on, on every call of \`Valid\`. -/
theorem loop_resources_of_eraseLoop {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {sel : Nat} {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (h : eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    (o : Oracle) (ho : SourceAsk ev o)
    {q : Assemble.Program} {scope : Call → Prop}
    (backend : Stage (mirSem o) (evmirSem o) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    {Valid : Call → Prop} (hvalid : ∀ call, Valid call → SelCall sel fn ws call)
    {code : ByteArray} {cert : Assemble.Cert} {mx : List Nat} {R : LoopRecord} {Eb Bb Xb M G : Nat}
    (hv : Verify.Gas.FixedFuel.verdictOf (some M) (Verify.Gas.FixedFuel.perIterGas cert Bb)
      (Verify.Gas.FixedFuel.exitGas cert Eb Xb) = .bounded G)
    (hc : AssembleLoop.checkL q code cert mx = true)
    (hok : cert.env = true → Assemble.OracleOk o) (henv : cert.reads = true → Assemble.EnvOk o)
    (loops : ∀ call, Valid call →
      Verify.Gas.FixedFuel.Loops (EVM.Program.block o call q) (0, [], State.initial call) R Eb Bb Xb M) :
    Shapes.Resources (solidCoreRuntime fuel) c code Valid (fun _ => G) := by
  have total : ∀ call, Valid call → ∃ obs, (solidCoreRuntime fuel).run c call = some obs := by
    intro call hcall
    obtain ⟨σ, args, ha, rfl⟩ := hvalid call hcall
    exact ⟨_, runs_of_bodyRuns hsel hfind hw hret (bodyRuns_of_eraseLoop h) hT σ ha⟩
  exact Verify.Gas.FixedFuel.resources_of_verdict hv hc o hok henv total
    ((source_edge_of_eraseLoop hsel hfind hw hret h hT hchk hobl hA o ho backend hscope).mono hvalid)
    loops

end Verify.LoopSource.Equiv

/-- info: 'Verify.LoopSource.Equiv.loop_resources_of_eraseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_resources_of_eraseLoop

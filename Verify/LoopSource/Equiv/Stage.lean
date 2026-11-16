import Verify.LoopSource.Equiv.Run
import Verify.LoopSource.Generic.Link
import Verify.ShapeGeneric

/-!
# The loop's source-to-MIR stage, and \`Shapes.Equiv\` for a loop-carrying function

\`loop_stage\`: a function whose body runs to the tree \`T\` (\`BodyRuns\`, the loop route's product)
and whose lowered MIR has a cut-point certificate that checks (\`Cut.check\`), with its leaves'
obligations (\`Obl\`), is compiled to MIR without changing a result: on every valid call, under
every oracle the flags allow, the module runs to the source's observable. Both sides are the
tree's observable at the call's words: the source by \`runs_of_bodyRuns\`, the MIR by
\`loop_mir_runs\`.

\`loop_equiv\` composes it with the backend's MIR-to-EVM-IR stage and the assembler's loop checker
(\`AssembleLoop.checkL\`), the two stages the driver proves for every program, loop-free or not, as
\`ShapeGeneric.compiled_of\` does: the driver's \`Shapes.Equiv\`. Nothing here takes \`Equiv\`, or a
source-to-anything stage, as a premise.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar

/-- **The loop's source-to-MIR stage.** -/
theorem loop_stage {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {sel : Nat}
    {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    (o : Oracle) (ho : SourceAsk ev o) :
    Stage (solidCoreRuntime fuel) (mirSem o) c m (SelCall sel fn ws) := by
  rintro _ ⟨σ, args, ha, rfl⟩ obs hs
  rw [runs_of_bodyRuns hsel hfind hw hret hb hT σ ha] at hs
  obtain rfl := Option.some.inj hs
  obtain ⟨hlen, hargs, hcl⟩ := ha
  have hc := (callFacts sel hsel args hargs σ).at
  rw [← hlen] at hchk hobl
  exact loop_mir_runs hchk hobl hc rfl (hA σ args ⟨hlen, hargs, hcl⟩) o (ho.envAsk args (slotValue σ))

/-- **\`Shapes.Equiv\` for a loop-carrying function**: the loop's source-to-MIR stage, the backend's
MIR-to-EVM-IR stage and the assembler's loop checker. -/
theorem loop_equiv {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {sel : Nat}
    {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat}
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true) :
    Shapes.Equiv (solidCoreRuntime fuel) c code (SelCall sel fn ws) := by
  have total : ∀ call, SelCall sel fn ws call → ∃ obs, (solidCoreRuntime fuel).run c call = some obs := by
    rintro _ ⟨σ, args, ha, rfl⟩
    exact ⟨_, runs_of_bodyRuns hsel hfind hw hret hb hT σ ha⟩
  have src := loop_stage hsel hfind hw hret hb hT hchk hobl hA Shapes.oracle
    Shapes.oracle_sourceEnvOk.ask
  have stage : Stage (solidCoreRuntime fuel) (evmirSem Shapes.oracle) c q (SelCall sel fn ws) :=
    src.trans (backend.mono hscope)
  exact Shapes.equiv_of_runs (sem := evmirSem) (q := fun _ => q) (Ok := fun o => o = Shapes.oracle) total
    (fun o ho => ho ▸ stage)
    (fun gas _ call _ => ⟨Shapes.oracle, rfl,
      AssembleLoop.within_of_checkL asm Shapes.oracle (fun _ => Shapes.oracle_ok.1) _ gas
        (fun _ => Shapes.oracle_ok.2)⟩)

end Verify.LoopSource.Equiv

/-- info: 'Verify.LoopSource.Equiv.loop_mir_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_mir_runs

/-- info: 'Verify.LoopSource.Equiv.loop_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_stage

/-- info: 'Verify.LoopSource.Equiv.loop_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_equiv

import Verify.ShapeGeneric
import SolidCore.Refinement.Solar.AssembleKnown

/-!
# The certified shape, through the checker with constants known across blocks

`ShapeGeneric`'s `compiled_of`, `compiled` and `compiled0` with `AssembleLoop.checkK` in place of
`checkL`: the same evidence, the same oracle, the same gas bound `gasBoundL cert N`, with
`within_of_checkK` for equivalence and `stage_of_checkK_gas` for resources. The certify driver uses
them only for a final EVM IR `checkL` refuses because it reaches memory at an offset the code keeps
on the stack from one block to another (tools/certify/asm_cert.py); `checkL`'s route is unchanged
and comes first.
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Solar SolidCore.Solidity

/-- **The shape from a total source stage, the backend stages and the checker with constants known
across blocks.** -/
theorem compiled_ofK {S : Sem} {p : S.Prog} {m : MIR.Lowered.moduleLayer.Prog}
    {q : Assemble.Program} {code : ByteArray} {Valid scope : Call → Prop} {c : Assemble.Cert}
    {mx : List Nat} {kn : List AssembleLoop.Known} {N : Nat}
    (inhabited : ∃ call, Valid call)
    (src : Stage S (mirSem oracle) p m Valid) (defined : Defined S p Valid)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, Valid call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkK q code c mx kn = true)
    (hG : AssembleLoop.gasBoundL c N < 2 ^ 64) :
    Compiled S p code Valid (fun _ => AssembleLoop.gasBoundL c N) := by
  have total : ∀ call, Valid call → ∃ obs, S.run p call = some obs := fun call hc =>
    Option.isSome_iff_exists.mp (defined call hc)
  have stage : Stage S (evmirSem oracle) p q Valid :=
    src.trans (backend.mono hscope)
  have hequiv : Equiv S p code Valid :=
    equiv_of_runs (sem := evmirSem) (q := fun _ => q) (Ok := fun o => o = oracle) total
      (fun o ho => ho ▸ stage)
      (fun gas _ call _ => ⟨oracle, rfl,
        AssembleLoop.within_of_checkK asm oracle (fun _ => oracle_ok.1) _ gas
          (fun _ => oracle_ok.2)⟩)
  have hres : Resources S p code Valid (fun _ => AssembleLoop.gasBoundL c N) :=
    resources_of_forward (B := evmirSem oracle) (q := q) total stage fun call _ =>
      ⟨hG, fun _ h1 _ obs hrun =>
        AssembleLoop.stage_of_checkK_gas asm oracle (fun _ => oracle_ok.1)
          (fun _ => oracle_ok.2) call N (Option.isSome_iff_exists.mp (ends call)) h1 obs hrun⟩
  exact ⟨inhabited, equivG_of hequiv hres, fun call hc => by
    obtain ⟨obs, hs⟩ := total call hc
    exact ⟨obs, hs, trivial⟩, hres⟩

/-- **The shape of a generic-stage contract**, through `checkK`. -/
theorem compiledK {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {kn : List AssembleLoop.Known} {N : Nat}
    (inhabited : ∃ call, genericValid fns s call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkK q code cert mx kn = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCore fuel) c code (genericValid fns s) (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_ofK inhabited
    (Generic.stageAtValueWith oracle hd oracle_sourceEnvOk.ask hchk hval)
    (Generic.definedAtValue hd hchk hval) backend hscope ends asm hG

/-- **The shape of a generic-stage contract on calls without a value**, through `checkK`. -/
theorem compiled0K {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {kn : List AssembleLoop.Known} {N : Nat}
    (inhabited : ∃ call, genericValid0 fns s call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid0 fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkK q code cert mx kn = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCore fuel) c code (genericValid0 fns s) (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_ofK inhabited (Generic.stageAtWith oracle hd oracle_sourceEnvOk.ask hchk)
    (Generic.definedAt hd hchk) backend hscope ends asm hG

/-- info: 'SolidCore.Refinement.Shapes.compiledK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiledK

/-- info: 'SolidCore.Refinement.Shapes.compiled0K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled0K

end SolidCore.Refinement.Shapes

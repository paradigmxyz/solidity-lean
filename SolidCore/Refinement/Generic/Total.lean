import SolidCore.Refinement.Generic.Stage
import SolidCore.Refinement.Behaviours

/-!
# The generic source stage is total

`Generic.stageAtWith` is a forward stage, so on its own it would say nothing about a call SolidCore
does not finish. Its proof shows more: on every call of its scope SolidCore finishes, with the
observable of the erased function tree (`source_run`). `definedAt` records that, and
`totalAtWith` (with its corollaries for each environment flag) states the stage as a total
refinement (`SolidCore.Refinement.Total`): on every call of the scope both SolidCore and the lowered MIR
module finish, with the same observable, so the module's behaviours there are SolidCore's
(`Total.backward`). A chain that starts with this stage is total whatever stages follow it
(`Total.trans_stage`).
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi

/-- SolidCore finishes every call of the generic stage's scope that `check` accepts. -/
theorem definedAt {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} {env : EnvFlags} (hchk : check fuel mirFuel c.core m fns env = true) :
    Defined (solidCore fuel) c (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩
  have hcf := List.all_eq_true.mp hchk f hf
  unfold checkFn at hcf
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : eraseFn (envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  cases ht2 : symTree m f.sel f.params.length mirFuel env with
  | none => simp [hfind, ht1, ht2] at hcf
  | some t2 =>
  simp only [hfind, ht1, ht2, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, -⟩ := hcf
  have hsrc := source_run hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs
  change (Source.run fuel c _).isSome = true
  rw [hsrc]
  rfl

/-- SolidCore finishes every call of the scope from any storage, for a constructor that leaves no
storage. -/
theorem defined {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    {env : EnvFlags} (hchk : check fuel mirFuel c.core m fns env = true) :
    Defined (solidCore fuel) c (fun call => ∃ σ, fullScope fns σ call) :=
  fun call ⟨σ, h⟩ => definedAt hd hchk call ⟨σ, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- **The generic source stage, total**: on every call of the scope, SolidCore and the module
both finish, with the same observable. -/
theorem totalAtWith (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : check fuel mirFuel c.core m fns env = true) :
    Total (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  total_iff_stage.mpr ⟨stageAtWith o hd henv hchk, definedAt hd hchk⟩

theorem totalAt (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true) :
    Total (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  totalAtWith o hd SourceAsk.off hchk

theorem totalAtEnv (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .all = true) :
    Total (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  totalAtWith o hd henv.ask hchk

theorem totalAtCaller (o : Oracle) (henv : CallerOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .callerOnly = true) :
    Total (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  totalAtWith o hd henv.ask hchk


/--
info: 'SolidCore.Refinement.Generic.totalAtWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms totalAtWith

end SolidCore.Refinement.Generic

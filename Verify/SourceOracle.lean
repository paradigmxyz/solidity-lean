import Verify.Final
import SolidCore.Refinement.SourceOracle
import SolidCore.Refinement.Generic.StageIn
import SolidCore.Refinement.SourceOracleSat
import SolidCore.Refinement.SourceOracleMono

/-!
# The composition under a call oracle

`compose_in` is `Final.compose_anyGas` for SolidCore in the world `W` (`solidCoreIn`), with the
oracle hypothesis `CallsAgree o W` that the source stage into `mirSem o` assumes a premise of the
end-to-end theorem: a specification proved of SolidCore under every open world, or under the
worlds a named interface hypothesis admits, holds of the bytecode for every oracle that agrees with
one of them.
-/

namespace SolidCore.Refinement

/-- **The specification holds of the bytecode, in the world `W`**: given the specification of
SolidCore in `W`, its totality there, the source stage into `mirSem o` under the oracle hypothesis
`CallsAgree o W`, the backend stages and the assembly stage at every gas, the bytecode agrees with
SolidCore in `W` and the specification holds of it at every gas. -/
theorem compose_in {St : Type} {W : World} {fuel : Nat} {o : SolarTV.Machine.Oracle}
    {mirSem evmirSem : Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mir : mirSem.Prog} {evmir : evmirSem.Prog} {code : ByteArray}
    {spec : Final.ContractSpec St}
    (agree : CallsAgree o W)
    (source : Final.Holds (solidCoreIn W fuel) c spec)
    (fin : ∀ call, spec.Calls call → (Source.runIn W fuel c call).isSome)
    (lowering : CallsAgree o W → Stage (solidCoreIn W fuel) mirSem c mir spec.Calls)
    (backend : Stage mirSem evmirSem mir evmir spec.Calls)
    (assembly : ∀ gas, Final.Within evmirSem (Final.ethLibWith gas) evmir code spec.Calls)
    (gas : Nat) :
    Final.Within (solidCoreIn W fuel) (Final.ethLibWith gas) c code spec.Calls ∧
      Final.Holds (Final.ethLibWith gas) code spec :=
  Final.compose_anyGas source fin (lowering agree) backend assembly gas

/-- info: 'SolidCore.Refinement.compose_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_in

/-- **The specification holds of the bytecode, run by run**: a call's outcomes in EthLib depend on
the gas and the state of the other accounts, so no single oracle describes every run. Here each run
of the bytecode at each gas has an oracle `o` and an open world `W` that agree (`CallsAgree o W`)
under which the EVM IR gives the bytecode's result or a failure that changes nothing (`assembly`);
the specification, the totality and the stages hold for every open world and every oracle; and then
the specification holds of the bytecode at every gas. -/
theorem holds_of_runs {St : Type} {fuel : Nat}
    {mirSem evmirSem : SolarTV.Machine.Oracle → Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mir : ∀ o, (mirSem o).Prog} {evmir : ∀ o, (evmirSem o).Prog} {code : ByteArray}
    {spec : Final.ContractSpec St}
    (source : ∀ W : World, W.Open → Final.Holds (solidCoreIn W fuel) c spec)
    (fin : ∀ W : World, W.Open → ∀ call, spec.Calls call → (Source.runIn W fuel c call).isSome)
    (lowering : ∀ o W, CallsAgree o W → Stage (solidCoreIn W fuel) (mirSem o) c (mir o) spec.Calls)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) (mir o) (evmir o) spec.Calls)
    (assembly : ∀ gas call, spec.Calls call → ∃ o W, W.Open ∧ CallsAgree o W ∧
      Final.Within (evmirSem o) (Final.ethLibWith gas) (evmir o) code (· = call))
    (gas : Nat) : Final.Holds (Final.ethLibWith gas) code spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  have hc : spec.Calls (f.call args v σ) := ⟨f, hf, args, ht, v, hv, σ, rfl⟩
  obtain ⟨o, W, hopen, hagree, hwithin⟩ := assembly gas _ hc
  have agree := Final.agree_of_stage ((lowering o W hagree).trans (backend o)) (fin W hopen)
  rcases hwithin _ rfl obs hrun with h | ⟨hs, hst, hl⟩
  · obtain ⟨obs', hs', hm⟩ := agree _ hc
    rw [h] at hm
    cases hm
    exact source W hopen f hf args ht v hv σ hinv hreq obs hs'
  · exact ⟨fun h'' => absurd (hs.symm.trans h'') (by decide), fun _ => ⟨hst, hl⟩⟩

/-- info: 'SolidCore.Refinement.holds_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_runs

/-- **The specification holds of the bytecode, run by run, for a contract the generic check
accepts**: `holds_of_runs` with its lowering obligation discharged by the generic source stage in
every world (`Generic.stageInDeployed`): the functions `check` accepts make no external call, so the
stage holds for every world and oracle with no hypothesis. -/
theorem holds_of_runs_generic {St : Type} {fuel mirFuel : Nat}
    {evmirSem : SolarTV.Machine.Oracle → Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)}
    {m : SolarTV.MIR.Lowered.Module} {fns : List Abi.Fn}
    {evmir : ∀ o, (evmirSem o).Prog} {code : ByteArray} {spec : Final.ContractSpec St}
    (hd : Wide.DeployedAt fuel c d s) (hchk : Generic.check fuel mirFuel c.core m fns = true)
    (hscope : ∀ call, spec.Calls call → Abi.fullScope fns s call)
    (source : ∀ W : World, W.Open → Final.Holds (solidCoreIn W fuel) c spec)
    (fin : ∀ W : World, W.Open → ∀ call, spec.Calls call → (Source.runIn W fuel c call).isSome)
    (backend : ∀ o, Stage (SolarTV.MIR.Lowered.moduleSem o) (evmirSem o) m (evmir o) spec.Calls)
    (assembly : ∀ gas call, spec.Calls call → ∃ o W, W.Open ∧ CallsAgree o W ∧
      Final.Within (evmirSem o) (Final.ethLibWith gas) (evmir o) code (· = call))
    (gas : Nat) : Final.Holds (Final.ethLibWith gas) code spec :=
  holds_of_runs (mirSem := SolarTV.MIR.Lowered.moduleSem) (mir := fun _ => m) source fin
    (fun o W _ => SolarTV.Stage.mono (Generic.stageInDeployed W o hd hchk) hscope)
    backend assembly gas

/-- info: 'SolidCore.Refinement.holds_of_runs_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_runs_generic

/-! ## Specifications in every world -/

/-- `Triple` with SolidCore in the world `W`. -/
def TripleIn (W : World) (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (scope : SolarTV.Call → Prop) (pre : SolarTV.Call → Prop)
    (post : SolarTV.Call → SolarTV.Observable → Prop) : Prop :=
  ∀ call, scope call → pre call →
    (Source.runIn W fuel c call).isSome ∧
      ∀ obs, Source.runIn W fuel c call = some obs → post call obs

/-- **A triple of a function the generic check accepts holds in every world**: such a function runs
the same in every world (`Generic.runIn_eq_run`). -/
theorem tripleIn_of_triple {fuel mirFuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)} {m : SolarTV.MIR.Lowered.Module}
    {fns : List Abi.Fn} {env : SolidCore.Refinement.Generic.EnvFlags}
    (hd : Wide.DeployedAt fuel c d s) (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    {scope pre : SolarTV.Call → Prop} {post : SolarTV.Call → SolarTV.Observable → Prop}
    (hscope : ∀ call, scope call → ∃ σ, Generic.Covers s σ ∧ Abi.fullScope fns σ call)
    (h : SolidCore.Verify.Triple fuel c scope pre post) (W : World) :
    TripleIn W fuel c scope pre post := by
  intro call hs hp
  rw [Generic.runIn_eq_run W hd hchk call (hscope call hs)]
  exact h call hs hp

/-- **A specification of the functions the generic check accepts holds in every world.** -/
theorem holdsIn_of_holds {St : Type} {fuel mirFuel : Nat}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State}
    {s : List (Nat × Nat)} {m : SolarTV.MIR.Lowered.Module} {fns : List Abi.Fn}
    {env : SolidCore.Refinement.Generic.EnvFlags} {spec : Final.ContractSpec St}
    (hd : Wide.DeployedAt fuel c d s) (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hscope : ∀ call, spec.Calls call → ∃ σ, Generic.Covers s σ ∧ Abi.fullScope fns σ call)
    (h : Final.Holds (solidCore fuel) c spec) (W : World) :
    Final.Holds (solidCoreIn W fuel) c spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  have hc : spec.Calls (f.call args v σ) := ⟨f, hf, args, ht, v, hv, σ, rfl⟩
  change Source.runIn W fuel c _ = some obs at hrun
  rw [Generic.runIn_eq_run W hd hchk _ (hscope _ hc)] at hrun
  exact h f hf args ht v hv σ hinv hreq obs hrun

/-- info: 'SolidCore.Refinement.tripleIn_of_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tripleIn_of_triple

/-- info: 'SolidCore.Refinement.holdsIn_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsIn_of_holds

end SolidCore.Refinement

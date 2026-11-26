import Verify.LoopSource.Equiv.CtorBridgeFrom
import Verify.LoopSource.Equiv.WithinFrom
import Verify.LoopSource.Equiv.CounterLoad
import Verify.LoopSource.Equiv.CounterCtor
import Verify.LoopSource.Equiv.Counter.Obl
import Verify.LoopSource.Equiv.Counter.Resources
import Verify.LoopSource.Equiv.Counter.Proofs.Stages
import Verify.LoopSource.Equiv.From.VC
import Verify.LoopSource.Equiv.From.Tree
import Verify.LoopSource.Equiv.From.CtxGas
import Verify.ShapeCtxGasFrom
import Verify.Generic.Expected

/-!
# Counter.bump: the expected theorem for every caller, on bounded calls

\`counter_expected\`: \`Expected\` for Counter deployed with \`[n]\` (\`n ∈ {5, 8}\`, the pinned words),
the spec \`spec n K\` (\`K ≤ Kmax\`) and the exact emitted runtime bytes, for every context \`ctx.Ok\`
(any caller below \`2 ^ 160\` but the contract) with:

* **valid calls** \`bump(a)\` with \`a ≤ K\` (\`BumpCallBounded K\`, the scope's iteration bound), call
  value 0 (in \`bumpCall\`), any storage that writes slot 1 when \`n ≠ 0\` (the load cover of the
  deployment the constructor leaves);
* **equivalence** at every gas (\`within_of_checkXLFrom\`), **termination**, the **postcondition**
  \`BumpPost\` and **resources** \`G K\` from the caller (\`forward_of_checkXLFrom\` via
  \`gasEdge_ofXL\`), each through: the deployed source from the caller (\`deployed_run_entry_from\`,
  load-level deployment \`counter_load_deployed\`), its loop from the symbolic caller
  (\`From.VC.body_runs_vc\`), the MIR (\`loop_mir_runs\`, caller-independent), the backend stage
  (\`counterLoop_mir_to_evmir\`) and the checker with contexts and gas (\`From.CtxGas.check_ok\`).

and, from the lifecycle statement \`hl\` (a named premise, the generated lifecycle certificate),
the creation code with the pinned words deploys the runtime (\`run_of_statement\` with the typed
admission \`counter_admits\`). Unbounded calls, other call values and \`DeployedAtWith\` stay OPEN.
-/

namespace Verify.LoopSource.Equiv.CounterCtx
open SolarTV SolarTV.Machine SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar Contracts.VerifyCounter.Source
open SolidCore.Verify.Generic
open Verify.LoopSource.Equiv.CounterLoad

/-! ## The postcondition at any caller word -/

/-- The postcondition at caller word `x`: `bump`'s tree never reads the caller, so this is
`MirLink.tree_post` at the pinned tree. -/
theorem tree_post_at (x : Nat) {T : Tree} (hT : brTree bumpFn (argFacts [256] 0) bumpBr = some T)
    (σ : List (Nat × Nat)) {a : Nat} (ha : a < 2 ^ 256) :
    Verify.LoopSource.MirLink.BumpPost (Verify.LoopSource.MirLink.bumpCall σ a)
      (T.eval ⟨[a], slotValue σ, solHash, x⟩).obs := by
  obtain rfl := Option.some.inj (hT.symm.trans Verify.LoopSource.Equiv.CounterObl.tree)
  exact Verify.LoopSource.MirLink.tree_post _ Verify.LoopSource.Equiv.CounterObl.tree σ a ha

/-! ## Valuations, calls, cover -/

/-- The valuation of \`bump(a)\` from storage \`σ\` sent by caller word \`x\`. -/
def ρOf (σ : List (Nat × Nat)) (a x : Nat) : Val := ⟨[a], slotValue σ, solHash, x⟩

theorem callFactsAt (σ : List (Nat × Nat)) {a : Nat} (ha : a < 2 ^ 256) (x : Nat) :
    CallFactsAt (.w (.lit 0)) bumpSel 1 (ρOf σ a x) (Verify.LoopSource.MirLink.bumpCall σ a) := by
  have h := callFacts bumpSel (by decide) [a] (by simpa using ha) σ
  exact CallFacts.at ⟨h.value, h.size, h.args, h.selector, h.store, h.ok⟩

/-- The call writes slot 1 when the deployment's \`n\` is nonzero. -/
def CoverN (n : Nat) (σ : List (Nat × Nat)) : Prop := n ≠ 0 → ∃ kv ∈ σ, kv.1 % 2 ^ 256 = 1

theorem coversLoad {n : Nat} {d : Source.State} (hl : ∀ k, d.loadSlot k = if k % 2 ^ 256 = 1 then n else 0)
    {σ : List (Nat × Nat)} (h : CoverN n σ) : CoversLoad d σ := by
  intro k hk
  rw [hl k] at hk
  split at hk
  · rename_i h1
    obtain ⟨kv, hm, he⟩ := h hk
    exact ⟨kv, hm, by show kv.1 % 2 ^ 256 = k % 2 ^ 256; rw [he, h1]⟩
  · exact absurd rfl hk

/-! ## The source, from any caller -/

theorem fixObs_at (σ : List (Nat × Nat)) (args : List Nat) (x : Nat) (T : Tree) :
    fixObs σ (T.eval ⟨args, slotValue σ, solHash, x⟩).obs = (T.eval ⟨args, slotValue σ, solHash, x⟩).obs := by
  unfold fixObs
  split
  · rfl
  · rename_i h
    simp only [Res.obs, Bool.not_eq_true] at h ⊢
    rw [eval_store_of_fail _ T h]

theorem bodyRunsFrom {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    BodyRunsFrom { envOf c.core with facts := argFacts [256] 0 } fuel bumpFn Verify.LoopSource.Equiv.From.bumpBr := by
  obtain ⟨hf, -, -⟩ := shape_of hc
  have hE : ({ envOf c.core with facts := argFacts [256] 0 } : EraseEnv) =
      Verify.LoopSource.Equiv.From.env c.core.eventDecls c.core.table := by
    simp only [envOf, Verify.LoopSource.Equiv.From.env, hf]
    rfl
  rw [hE]
  exact Verify.LoopSource.Equiv.From.VC.body_runs_vc _ _ bumpFn rfl rfl _ (by unfold fuel; omega)

theorem treeFrom : brTree bumpFn (argFacts [256] 0) Verify.LoopSource.Equiv.From.bumpBr = some Verify.LoopSource.Equiv.CounterObl.T := by
  have h := Verify.LoopSource.Equiv.From.tree_eq
  have e : Verify.LoopSource.Equiv.CounterSummary.fn = bumpFn := rfl
  rw [e] at h
  rw [h]
  exact Verify.LoopSource.Equiv.CounterObl.tree

/-- **The deployed source's run of \`bump(a)\` from caller \`x\`**: the tree's observable at \`x\`. -/
theorem src_run {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} {d : Source.State}
    (hd : LoadDeployed fuel c [n] d) (hl : ∀ k, d.loadSlot k = if k % 2 ^ 256 = 1 then n else 0)
    (x : Nat) {σ : List (Nat × Nat)} (hcov : CoverN n σ) {a : Nat} (ha : a < 2 ^ 256) :
    SolidCore.Refinement.Source.runFromArgs x fuel [n] c (Verify.LoopSource.MirLink.bumpCall σ a) =
      some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a x)).obs := by
  have hw : widthsOf bumpFn.params bumpFn.paramAbiCleanups = some [256] := rfl
  obtain ⟨-, hargs, hclean⟩ := Verify.LoopSource.MirLink.args_one ha
  have hdec := decode_args hw [a] rfl hargs
  rw [if_pos hclean] at hdec
  have h := deployed_run_entry_from x hd (getD_load_cover (coversLoad hl hcov)) (slotValue_store σ)
    (by decide) (shape_of hc).2.2 hw rfl (bodyRunsFrom hc) treeFrom [a] rfl hargs hclean hdec
  rw [fixObs_at] at h
  exact h

/-! ## MIR and EVM IR, from any caller -/

theorem evmir_run (o : Oracle) (σ : List (Nat × Nat)) {a : Nat} (ha : a < 2 ^ 256) (x : Nat) :
    (evmirSem o).run SolarTV.Export.Counter.evm7 (Verify.LoopSource.MirLink.bumpCall σ a) =
      some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a x)).obs := by
  have hmir : (mirSem o).run SolarTV.Export.Counter.stage0 (Verify.LoopSource.MirLink.bumpCall σ a) =
      some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a x)).obs :=
    loop_mir_runs Verify.LoopSource.Equiv.CounterObl.leaves Verify.LoopSource.Equiv.CounterObl.obl (callFactsAt σ ha x) rfl trivial o
      ⟨fun h => by simp [EnvFlags.off] at h, fun h => by simp [EnvFlags.off] at h⟩
  exact SolarTV.Milestone.X.counterLoop_mir_to_evmir o _ trivial _ hmir

/-! ## The checker with contexts and gas -/

theorem guard_nil (p : Assemble.Program) : AssembleCtxGas.guard [] p = p := by
  cases p with
  | mk blocks =>
    simp only [AssembleCtxGas.guard, List.contains_nil, Bool.false_eq_true, ↓reduceIte]
    congr 1
    induction blocks with
    | nil => rfl
    | cons b bs ih => simp [List.mapIdx_cons, ih]

/-- The guarded, normalized final EVM IR runs as the final EVM IR. -/
theorem run_guard (o : Oracle) (call : Call) (N : Nat) :
    EVM.Program.run o (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F (AssembleCtx.norm SolarTV.Export.Counter.evm7)) call N =
      EVM.Program.run o SolarTV.Export.Counter.evm7 call N := by
  show EVM.Program.run o (AssembleCtxGas.guard [] _) call N = _
  rw [guard_nil, AssembleCtx.run_norm]

/-- The iteration bound's fuel. -/
abbrev N (K : Nat) : Nat := Verify.Gas.FixedFuel.fixedFuel 2 2 3 K

theorem ends {K : Nat} (o : Oracle) {call : Call} (hv : Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K call) :
    ∃ r, EVM.Program.run o (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
      (AssembleCtx.norm SolarTV.Export.Counter.evm7)) call (N K) = some r := by
  rw [run_guard]
  exact Verify.LoopSource.Equiv.CounterResources.ends o hv

/-! ## The gas bound -/

/-- **The gas bound** at iteration bound \`K\`. -/
def G (K : Nat) : Nat := AssembleLoop.gasBoundL Verify.LoopSource.Equiv.From.CtxGas.cx.base (N K)

/-- The largest bound below \`2 ^ 64\`. -/
def Kmax : Nat := 12274916205553

theorem G_eq (K : Nat) : G K = (2 * K + 5) * (22100 * AssembleLoop.bmax Verify.LoopSource.Equiv.From.CtxGas.cx.base) +
    EthLib.Execution.Evm.memoryGasCost Verify.LoopSource.Equiv.From.CtxGas.cx.base.top := by
  unfold G AssembleLoop.gasBoundL N Verify.Gas.FixedFuel.fixedFuel; ring_nf

theorem G_lt {K : Nat} (hK : K ≤ Kmax) : G K < 2 ^ 64 := by
  have hb : AssembleLoop.bmax Verify.LoopSource.Equiv.From.CtxGas.cx.base = 34 := by decide
  have hm : EthLib.Execution.Evm.memoryGasCost Verify.LoopSource.Equiv.From.CtxGas.cx.base.top = 12 := by decide
  rw [G_eq, hb, hm]; unfold Kmax at hK; omega

/-! ## The statement -/

/-- The valid calls: \`bump(a)\`, \`a ≤ K\`, no value, storage writing slot 1 when \`n ≠ 0\`. -/
def valid (n K : Nat) (call : Call) : Prop :=
  Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K call ∧ CoverN n call.storage

/-- The statuses allowed: a failure changes nothing. -/
def allowed (call : Call) (obs : Observable) : Prop :=
  obs.success = false → obs.storage = slotValue call.storage ∧ obs.logs = []

/-- **The specification** at iteration bound \`K\`, for the deployment's \`n\`. -/
def spec (n K : Nat) : Spec where
  Contexts := Context.Ok
  entries := [("bump", fun _ call => ∃ σ a, call = Verify.LoopSource.MirLink.bumpCall σ a)]
  Valid := fun _ => valid n K
  Allowed := fun _ => allowed
  Post := fun _ => Verify.LoopSource.MirLink.BumpPost
  gas := fun _ _ => G K
  assumptions := []

/-- **The source**: Counter's source unit and \`fuel\`, deployed with \`[n]\`. -/
def src (n : Nat) : Source [n] := ⟨SolidCore.Refinement.Source.VerifyCounter.importedSourceUnit, "Counter", fuel⟩

theorem src_checked (n : Nat) : (src n).checked = contract? := rfl

theorem eval_logs_of_fail (ρ : Val) : ∀ T : Tree, (T.eval ρ).success = false → (T.eval ρ).logs = []
  | .halt ok _ _ _, h => by simp only [Tree.eval] at h ⊢; simp [h]
  | .ite c t e, h => by
    simp only [Tree.eval] at h ⊢
    split <;> rename_i hc <;> simp only [hc, ↓reduceIte] at h
    · exact eval_logs_of_fail ρ e h
    · exact eval_logs_of_fail ρ t h

theorem bump0_valid (n K : Nat) : valid n K (Verify.LoopSource.MirLink.bumpCall [(1, n)] 0) :=
  ⟨⟨[(1, n)], 0, Nat.zero_le _, Nat.two_pow_pos 256, rfl⟩, fun _ => ⟨(1, n), List.mem_singleton_self _, rfl⟩⟩

theorem covered (n K : Nat) : (spec n K).Covered := by
  refine ⟨⟨_, Context.default_ok⟩, fun _ h => h, ?_, ?_, ?_⟩
  · intro ctx _ e he
    simp only [spec, List.mem_singleton] at he
    subst he
    exact ⟨_, bump0_valid n K, _, _, rfl⟩
  · refine ⟨Context.default, _, ⟨true, [], [], fun _ => 2 ^ 256⟩, Context.default_ok, bump0_valid n K, ?_⟩
    rintro ⟨σ, a, ha, he, h⟩
    have hσ : σ = [(1, n)] := (congrArg Call.storage he).symm
    subst hσ
    have h1 := (h rfl).1
    have h0 : slotValue [(1, n)] 0 = 0 := by simp [slotValue]
    rw [h0] at h1
    change 2 ^ 256 = 0 + a at h1
    omega
  · refine ⟨Context.default, _, ⟨false, [], [], fun _ => 1⟩, Context.default_ok, bump0_valid n K, rfl, ?_⟩
    intro h
    have h1 := congrFun (h rfl).1 0
    have h0 : slotValue [(1, n)] 0 = 0 := by simp [slotValue]
    change 1 = slotValue [(1, n)] 0 at h1
    rw [h0] at h1
    exact absurd h1 (by decide)

/-- **Certified in every context**, from the load-level deployment. -/
theorem certifiedAt {n K : Nat} (hK : K ≤ Kmax) {c : TypeCheck.CheckedContract} (hc : contract? = .ok c)
    {d : Source.State} (hd : LoadDeployed fuel c [n] d)
    (hl : ∀ k, d.loadSlot k = if k % 2 ^ 256 = 1 then n else 0) (ctx : Context) (hctx : ctx.Ok) :
    CertifiedAt ((src n).semAt ctx) c ctx (runtimeCode SolarTV.Export.Counter.bytecode) (valid n K)
      allowed Verify.LoopSource.MirLink.BumpPost (fun _ => G K) := by
  have hrun : ∀ σ a, CoverN n σ → a < 2 ^ 256 →
      ((src n).semAt ctx).run c (Verify.LoopSource.MirLink.bumpCall σ a) =
        some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a ctx.caller)).obs :=
    fun σ a hcov ha => src_run hc hd hl ctx.caller hcov ha
  have hAB := Assemble.address_ne_self hctx.1 hctx.2
  set o := SolidCore.Refinement.Shapes.oracleFrom ctx.caller
  have hev : ∀ σ a, a < 2 ^ 256 →
      (evmirSem o).run (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F (AssembleCtx.norm SolarTV.Export.Counter.evm7))
        (Verify.LoopSource.MirLink.bumpCall σ a) = some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a ctx.caller)).obs := by
    intro σ a ha
    show (evmirSem o).run (AssembleCtxGas.guard [] _) _ = _
    rw [guard_nil, AssembleCtx.sem_norm]
    exact evmir_run o σ ha ctx.caller
  refine ⟨⟨⟨_, bump0_valid n K⟩, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- equivalence at every gas
    rintro gas - _ ⟨⟨σ, a, haK, ha, rfl⟩, hcov⟩ obs hobs
    obtain ⟨r, hr⟩ := ends o (K := K) ⟨σ, a, haK, ha, rfl⟩
    rcases AssembleCtxGas.within_of_checkXLFrom Verify.LoopSource.Equiv.From.CtxGas.check_ok ctx.caller hAB o
      (fun h => absurd h (by decide)) (by decide) _ (N K) r hr gas obs hobs with h | h
    · left
      have he := SolidCore.Refinement.Shapes.evmir_run_of_iterate hr
      rw [hev σ a ha] at he
      rw [hrun σ a hcov ha, h, (Option.some.inj he).symm]
    · right; exact h
  · rintro _ ⟨⟨σ, a, -, ha, rfl⟩, hcov⟩
    exact ⟨_, hrun σ a hcov ha, trivial⟩
  · -- resources from the caller
    rintro _ ⟨⟨σ, a, haK, ha, rfl⟩, hcov⟩
    refine ⟨G_lt hK, fun gas hg _ => ?_⟩
    obtain ⟨obs, h1, h2⟩ := SolidCore.Refinement.Shapes.gasEdge_ofXL (Valid := Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K)
      (N := N K) Verify.LoopSource.Equiv.From.CtxGas.check_ok (by decide)
      (fun o call hv => Option.isSome_iff_exists.mpr (ends o hv))
      (fun o call _ => by show _ = EVM.Program.run o (AssembleCtxGas.guard [] _) call _; rw [guard_nil])
      ctx.caller hctx.1 hctx.2 o (SolidCore.Refinement.Shapes.oracleFrom_ok hctx.1) _ ⟨σ, a, haK, ha, rfl⟩ gas hg
    rw [AssembleCtx.sem_norm, evmir_run o σ ha ctx.caller] at h1
    show Final.Target.runWithFrom ctx.caller gas Verify.LoopSource.Equiv.From.CtxGas.code _ = _
    rw [h2, ← Option.some.inj h1, hrun σ a hcov ha]
  · -- allowed statuses
    rintro _ ⟨⟨σ, a, -, ha, rfl⟩, hcov⟩ obs hobs
    rw [hrun σ a hcov ha] at hobs
    obtain rfl := Option.some.inj hobs
    intro hs
    exact ⟨eval_store_of_fail _ _ hs, eval_logs_of_fail _ _ hs⟩
  · -- the postcondition
    rintro _ ⟨⟨σ, a, -, ha, rfl⟩, hcov⟩ obs hobs
    rw [hrun σ a hcov ha] at hobs
    obtain rfl := Option.some.inj hobs
    exact tree_post_at ctx.caller Verify.LoopSource.Equiv.CounterObl.tree σ ha

/-- **Counter.bump, the expected theorem for every caller, on bounded calls**, deployed with the
pinned words \`[n]\`, \`n ∈ {5, 8}\`; and from the lifecycle statement, its creation code with those
words, typed-admitted, deploys the runtime. -/
theorem counter_expected {n : Nat} (hn : n = 5 ∨ n = 8) {K : Nat} (hK : K ≤ Kmax) :
    Expected (src n) (spec n K) SolarTV.Export.Counter.bytecode ∧
      ∀ c, contract? = .ok c → ∀ s, Verify.Lifecycle.Statement fuel c Verify.LoopSource.Equiv.CounterCtor.counterInit
        (runtimeCode SolarTV.Export.Counter.bytecode) [n] s →
        Deploys (Verify.Lifecycle.initArgs Verify.LoopSource.Equiv.CounterCtor.counterInit [n])
          (runtimeCode SolarTV.Export.Counter.bytecode) s := by
  have hn' : n < 2 ^ 256 := by rcases hn with rfl | rfl <;> decide
  refine ⟨⟨by decide, covered n K, fun _ ctx hctx => ?_⟩, fun c hc s hl => ?_⟩
  · obtain ⟨c, hc⟩ := contract_ok
    obtain ⟨d, hd, hl⟩ := counter_load_deployed hc hn'
    exact ⟨c, hc, certifiedAt hK hc hd hl ctx hctx⟩
  · exact (Source.run_of_statement (src := src n) hc (Verify.LoopSource.Equiv.CounterCtor.counter_admits hc hn) hl).1

end Verify.LoopSource.Equiv.CounterCtx

/-- info: 'Verify.LoopSource.Equiv.CounterCtx.counter_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterCtx.counter_expected

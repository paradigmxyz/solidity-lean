import Verify.LoopSource.Equiv.CtorBridge
import Verify.LoopSource.Equiv.EraseLoopFinal
import Verify.Generic.CtorWords
import Verify.ShapeGenericRuntime
import Verify.Gas.FixedFuel.Run
import Verify.Lifecycle.Symbolic

/-!
# Deployed loop statements, and the parts of a contract with loops

The loop route publishes, per loop function, `Shapes.Certified (Generic.Loop.solidCoreRuntime fuel)`:
SolidCore's dispatcher on the runtime code alone, from the call's storage, with no constructor. This
module gives what turns those per-function statements into one statement of the deployed contract.

**Deployment (E6).**
* `Shapes.Certified.fromArgs_of_runtime`: a statement over the runtime code becomes the same statement
  over `solidCoreFromArgs callerAddress fuel ws` (the contract SolidCore's constructor leaves on the
  argument words `ws`) on any valid calls on which the two runs agree; `Compiled.fromArgs_of_runtime`
  for the compiled shape.
* `Loop.runEq_of_erasedOf`: on a loop function the join's computed facts name (`erasedOf`, `sigOf`),
  from a load-level deployment (`LoadDeployed`) and a call storage covering it, the runs agree
  (`CtorBridge.semAt_eq_runtime_load`).
* `Loop.runEq_of_check`: the same on a function the generic source check accepts
  (`CtorWords.source_run_args` against `runtime_run_erased`).
* `Generic.deployed_of_ctorShapeOf_snd`: `deployed_of_ctorShapeOf`'s deployment from a check of the
  shape's flag alone, so a generated module needs no literal of the checked core.
* `Lifecycle.Creation.Sym.codeOf_of_consts`: a symbolic creation's runtime code with no argument byte
  is the same code for every argument list.

**Parts (E3).**
* `Shapes.compiled_of_ends`: `compiled_of` with its fuel premise on the valid calls only, so a program
  with loops elsewhere still states a loop-free function's calls.
* `Shapes.certified_part_runtime`: the statement of a loop-free function of a contract with loops,
  over the runtime code, from the generic source check, the backend, the loop checker and a fixed fuel
  bound (`Loops`, which a path tree with no loop gives) on its calls; no specification (allowed
  statuses and postcondition `True`).
* `Shapes.Certified.union_const`: two certified parts with constant gas bounds make one certified
  statement on the union of their valid calls, at the larger bound.

Fixed context only: the caller is `callerAddress` and the value 0, as every loop part's. Nothing here
names a contract. Every theorem is proved; no axiom is added.
-/

namespace SolidCore.Refinement.Shapes
open SolarTV SolidCore.Refinement SolidCore.Refinement.Solar SolidCore.Solidity
open SolidCore.Refinement.Generic.Loop

/-- **The runtime statement is the deployed contract's** on the valid calls on which the two runs
agree. -/
theorem Certified.fromArgs_of_runtime {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract}
    {code : ByteArray} {V V' : Call → Prop} {A P : Call → Observable → Prop} {G : Call → Nat}
    (h : Certified (solidCoreRuntime fuel) c code V A P G) (hsub : ∀ call, V' call → V call)
    (heq : ∀ call, V' call →
      (solidCoreFromArgs callerAddress fuel ws0).run c call = (solidCoreRuntime fuel).run c call)
    (hinh : ∃ call, V' call) :
    Certified (solidCoreFromArgs callerAddress fuel ws0) c code V' A P G where
  inhabited := hinh
  equiv := fun gas hg call hv obs hr => by
    have := h.equiv gas hg call (hsub call hv) obs hr
    rwa [← heq call hv] at this
  terminates := fun call hv => by
    have := h.terminates call (hsub call hv)
    rwa [← heq call hv] at this
  meets := fun call hv obs hr => h.meets call (hsub call hv) obs (by rw [← heq call hv]; exact hr)
  resources := fun call hv => by
    have := h.resources call (hsub call hv)
    rwa [← heq call hv] at this

/-- **The runtime compiled shape is the deployed contract's**, the same way. -/
theorem Compiled.fromArgs_of_runtime {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract}
    {code : ByteArray} {V V' : Call → Prop} {G : Call → Nat}
    (h : Compiled (solidCoreRuntime fuel) c code V G) (hsub : ∀ call, V' call → V call)
    (heq : ∀ call, V' call →
      (solidCoreFromArgs callerAddress fuel ws0).run c call = (solidCoreRuntime fuel).run c call)
    (hinh : ∃ call, V' call) :
    Compiled (solidCoreFromArgs callerAddress fuel ws0) c code V' G where
  inhabited := hinh
  equiv := fun gas hg call hv obs hr => by
    have := h.equiv gas hg call (hsub call hv) obs hr
    rwa [← heq call hv] at this
  terminates := fun call hv => by
    have := h.terminates call (hsub call hv)
    rwa [← heq call hv] at this
  resources := fun call hv => by
    have := h.resources call (hsub call hv)
    rwa [← heq call hv] at this

/-- **Two certified parts, one statement**: on the union of the valid calls, at the larger of two
constant gas bounds. -/
theorem Certified.union_const {S : Sem} {p : S.Prog} {code : ByteArray} {V₁ V₂ : Call → Prop}
    {A P : Call → Observable → Prop} {g₁ g₂ : Nat}
    (h₁ : Certified S p code V₁ A P (fun _ => g₁)) (h₂ : Certified S p code V₂ A P (fun _ => g₂)) :
    Certified S p code (fun call => V₁ call ∨ V₂ call) A P (fun _ => max g₁ g₂) := by
  have b₁ : g₁ < 2 ^ 64 := by
    obtain ⟨call, hc⟩ := h₁.inhabited
    exact (h₁.resources call hc).1
  have b₂ : g₂ < 2 ^ 64 := by
    obtain ⟨call, hc⟩ := h₂.inhabited
    exact (h₂.resources call hc).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨call, hc⟩ := h₁.inhabited
    exact ⟨call, Or.inl hc⟩
  · intro gas hg call hv obs hr
    rcases hv with hv | hv
    · exact h₁.equiv gas hg call hv obs hr
    · exact h₂.equiv gas hg call hv obs hr
  · intro call hv
    rcases hv with hv | hv
    · exact h₁.terminates call hv
    · exact h₂.terminates call hv
  · intro call hv obs hr
    rcases hv with hv | hv
    · exact h₁.meets call hv obs hr
    · exact h₂.meets call hv obs hr
  · intro call hv
    refine ⟨Nat.max_lt.mpr ⟨b₁, b₂⟩, fun gas hge hg => ?_⟩
    rcases hv with hv | hv
    · exact (h₁.resources call hv).2 gas (Nat.le_trans (Nat.le_max_left _ _) hge) hg
    · exact (h₂.resources call hv).2 gas (Nat.le_trans (Nat.le_max_right _ _) hge) hg

/-- **`compiled_of` with its fuel premise on the valid calls only.** -/
theorem compiled_of_ends {S : Sem} {p : S.Prog} {m : MIR.Lowered.moduleLayer.Prog}
    {q : Assemble.Program} {code : ByteArray} {Valid scope : Call → Prop} {c : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, Valid call)
    (src : Stage S (mirSem oracle) p m Valid) (defined : Defined S p Valid)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, Valid call → scope call)
    (ends : ∀ call, Valid call → (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code c mx = true)
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
        AssembleLoop.within_of_checkL asm oracle (fun _ => oracle_ok.1) _ gas
          (fun _ => oracle_ok.2)⟩)
  have hres : Resources S p code Valid (fun _ => AssembleLoop.gasBoundL c N) :=
    resources_of_forward (B := evmirSem oracle) (q := q) total stage fun call hc =>
      ⟨hG, fun _ h1 _ obs hrun =>
        AssembleLoop.stage_of_checkL_gas asm oracle (fun _ => oracle_ok.1)
          (fun _ => oracle_ok.2) call N (Option.isSome_iff_exists.mp (ends call hc)) h1 obs hrun⟩
  exact ⟨inhabited, equivG_of hequiv hres, fun call hc => by
    obtain ⟨obs, hs⟩ := total call hc
    exact ⟨obs, hs, trivial⟩, hres⟩

/-- **A loop-free function of a contract with loops**, over the runtime code: the generic source
check of its selector, the backend stage, the loop checker on the exact bytes and a fixed fuel bound
on its valid calls give equivalence, termination and resources; with no specification its allowed
statuses and postcondition are `True`. -/
theorem certified_part_runtime {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {m : MIR.Lowered.Module} {fns : List Abi.Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    {Valid : Call → Prop} (hsub : ∀ call, Valid call → ∃ σ, Abi.fullScope fns σ call)
    (hinh : ∃ call, Valid call)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    {R : Verify.LoopSource.Interface.LoopRecord} {E B X M : Nat}
    (loops : ∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B X M)
    (hG : AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B X M) < 2 ^ 64) :
    Certified (solidCoreRuntime fuel) c code Valid (fun _ _ => True) (fun _ _ => True)
      (fun _ => AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B X M)) := by
  have h := compiled_of_ends (S := solidCoreRuntime fuel) (p := c) hinh
    ((stageRuntimeWith oracle oracle_sourceEnvOk.ask hchk).mono hsub)
    (fun call hv => definedRuntime hchk call (hsub call hv))
    backend (fun call _ => hscope call)
    (fun call hv => Verify.Gas.FixedFuel.ends_fixed loops call hv) asm hG
  exact h.certified (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)

end SolidCore.Refinement.Shapes

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open Verify.LoopSource.Generic (selCall)

/-- **On a loop function the join's facts name, the deployed contract and the runtime code run
alike** on every clean call whose storage covers the deployment. -/
theorem runEq_of_erasedOf {c? : Verify.LoopSource.Equiv.GenObl.Checked} {sel fuel n : Nat} {b : Br}
    {Te : Tree} {ws : List Nat} (hsel : sel < 2 ^ 32)
    (hE : Verify.LoopSource.Equiv.GenObl.erasedOf c? sel fuel = some (n, b, Te))
    (hS : Verify.LoopSource.Equiv.EraseLoopFinal.sigOf c? sel = some (ws, true))
    {c : TypeCheck.CheckedContract} (hc : c? = .ok c) {ws0 : List Nat} {d : Source.State}
    (hd : LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)} {args : List Nat}
    (hl : args.length = n) (ha : ∀ a ∈ args, a < 2 ^ 256) (hcl : argsClean ws args = true)
    (hcov : CoversLoad d σ) :
    (solidCoreFromArgs callerAddress fuel ws0).run c (selCall sel σ args) =
      (solidCoreRuntime fuel).run c (selCall sel σ args) := by
  obtain ⟨c', fn, hc', hf, hw, hret, hn, he, ht⟩ :=
    Verify.LoopSource.Equiv.EraseLoopFinal.facts_of hE hS
  rw [hc] at hc'
  cases hc'
  exact semAt_eq_runtime_load hd hsel hf hw hret (bodyRuns_of_eraseLoop he) ht
    ⟨⟨σ, args, ⟨hl.trans hn.symm, ha, hcl⟩, rfl⟩, hcov⟩

/-- **On a function the generic source check accepts, the deployed contract and the runtime code
run alike** on every call of it from a storage covering the deployment. -/
theorem runEq_of_check {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {m : SolarTV.MIR.Lowered.Module} {fns : List Abi.Fn} {env : EnvFlags}
    (hchk : check fuel mirFuel c.core m fns env = true)
    {f : Abi.Fn} (hf : f ∈ fns) {ws0 : List Nat} {d : Source.State}
    (hd : LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)} (hcov : CoversLoad d σ)
    (args : List Nat) (hlen : args.length = f.params.length) (ha : ∀ a ∈ args, a < 2 ^ 256) :
    (solidCoreFromArgs callerAddress fuel ws0).run c
        { calldata := Abi.calldata f.sel args, callvalue := 0, storage := σ } =
      (solidCoreRuntime fuel).run c
        { calldata := Abi.calldata f.sel args, callvalue := 0, storage := σ } := by
  obtain ⟨hsel, fn, t1, -, hfind, hpl, ht1, -, -⟩ := check_mem hchk hf
  show Refinement.Source.runFromArgs callerAddress fuel ws0 c _ = runtimeRun fuel c _
  rw [source_run_args hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) ha,
    runtime_run_erased hsel hfind ht1 args (by rw [hlen, hpl]) ha]

end SolidCore.Refinement.Generic.Loop

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- **`deployed_of_ctorShapeOf` from the shape's flag alone.** -/
theorem deployed_of_ctorShapeOf_snd {fuel : Nat}
    {c? : Except TypeCheck.TypeError TypeCheck.CheckedContract} {wds : List Nat} {b : Br}
    {W : Writes} {c : TypeCheck.CheckedContract}
    (h : (ctorShapeOf fuel c? wds b W).map Prod.snd = some true) (hc : c? = .ok c) :
    (∀ ws, ws.length = wds.length → (∀ a ∈ ws, a < 2 ^ 256) → argsClean wds ws = true →
        CtorReturns fuel c? ws →
        ∃ d, Loop.LoadDeployed fuel c ws d ∧ ∀ σ, Covers (storageOf W ws) σ → Loop.CoversLoad d σ) ∧
      (∀ ws, ws.length = wds.length → (∀ a ∈ ws, a < 2 ^ 256) → argsClean wds ws = true →
        normalAt b ws = true → CtorReturns fuel c? ws) := by
  cases h' : ctorShapeOf fuel c? wds b W with
  | none => rw [h'] at h; cases h
  | some p =>
    obtain ⟨core, f⟩ := p
    rw [h'] at h
    cases h
    exact (deployed_of_ctorShapeOf h' hc).2

/-- A storage covers itself. -/
theorem covers_refl (s : List (Nat × Nat)) : Covers s s := fun kv hkv => ⟨kv, hkv, rfl⟩

end SolidCore.Refinement.Generic

namespace Verify.Lifecycle.Creation.Sym

/-- **A creation's runtime code with no argument byte** is the same bytes for every argument list. -/
theorem codeOf_of_consts {code : List B} {l : List UInt8} (h : consts code = some l)
    (as : List EthLib.Base.U256) : codeOf as code = ba l := by
  unfold codeOf bytesOf
  rw [consts_eval h]

end Verify.Lifecycle.Creation.Sym

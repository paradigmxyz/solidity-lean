import Verify.Fuel
import Verify.VC.Obligations

/-!
# Fuel: one fuel for every call, from a run at one fuel

`Verify.Fuel` keeps two notions apart: **for every call, some fuel** (`TripleSome`, `runAny`) and
**one fuel for every call** (`Triple fuel`). This module adds the uniform notion above a fuel:

* `UniformFrom n c scope`: on every call of `scope`, every fuel `m ≥ n` gives SolidCore's run at
  `n`, the same result, finished or not. It is a property of the scope's calls, not of every call
  of `c`, so it is weaker than `FuelStable c` and says nothing below `n`.
* `Triple.mono_of_uniform`: a triple at `n` is a triple at every `m ≥ n`.

and proves it for the generic source stage, where the fuel enters twice: in the constructor's run
(`Wide.DeployedAt fuel`) and in the erasure (`eraseFn _ fuel`, which runs a statement with the
fuel SolidCore runs it with).

* `eraseStmt_mono`, `eraseFn_mono` (proved): an erasure that finishes at fuel `n` is the same
  tree at every `m ≥ n`. The erasure counts fuel only to stop, so more fuel never changes a
  finished erasure.
* `DeployStable n c s`: the constructor leaves the entries `s` at every fuel `m ≥ n`. A
  hypothesis: the constructor runs through `constructWithContext?`, whose context installs a
  self-dispatch hook built from the fuel, so the interpreter-level monotonicity of
  `SolidCore.Solidity.FuelMonotonicity` (one tree, one context) does not reach it as stated.
* `uniformFrom_stage`: with `DeployStable`, every function the stage erases at fuel `n` runs
  every call of its scope the same at every `m ≥ n`: as its tree.
* `triple_of_binds_from`: the generic theorem from an erased function to its obligations
  (`triple_of_binds`), at every fuel from `n` on.

None of this turns "for every call, some fuel" into one fuel: `UniformFrom` is proved from one
fuel `n` that already finishes every call of the scope (`source_run` at `n`). A loop whose
calls need fuel that grows with their arguments has no such `n`; for it the honest statements
stay `TripleSome` and `TripleAny` (`Verify.Fuel`), or `TripleWithin B` with a bound `B`
proved for the contract.
-/

namespace SolidCore.Verify

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic SolidCore.Solidity

local notation "Br" => SolidCore.Refinement.Generic.Br
local notation "SymState" => SolidCore.Refinement.Generic.SymState

/-! ## Uniform fuel on a scope -/

/-- On every call of `scope`, every fuel from `n` on gives the run at `n`. -/
def UniformFrom (n : Nat) (c : TypeCheck.CheckedContract) (scope : Call → Prop) : Prop :=
  ∀ call, scope call → ∀ m, n ≤ m → Source.run m c call = Source.run n c call

/-- A triple at `n` is a triple at every fuel from `n` on, on a scope where the runs are
uniform from `n`. -/
theorem Triple.mono_of_uniform {n m : Nat} {c : TypeCheck.CheckedContract}
    {scope pre : Call → Prop} {post : Call → Observable → Prop}
    (hu : UniformFrom n c scope) (hnm : n ≤ m) (h : Triple n c scope pre post) :
    Triple m c scope pre post := by
  intro call hs hp
  rw [hu call hs m hnm]
  exact h call hs hp

/-! ## The erasure is monotone in its fuel -/

namespace Erase

theorem Br.bind_mono {k k' : SymState → Option Br}
    (hk : ∀ S r, k S = some r → k' S = some r) : ∀ {b r : Br}, b.bind k = some r → b.bind k' = some r
  | .leaf (.normal S), r, h => hk S r h
  | .leaf (.returned _ _), _, h => h
  | .leaf (.reverted _), _, h => h
  | .ite c t e, r, h => by
    simp only [Br.bind, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
    obtain ⟨t', ht, e', he, rfl⟩ := h
    exact ⟨t', Br.bind_mono hk ht, e', Br.bind_mono hk he, rfl⟩

theorem eraseSeq_mono {f g : SolidCore.Solidity.Source.Stmt → SymState → Option Br}
    (hfg : ∀ s S b, f s S = some b → g s S = some b) :
    ∀ (ss : List SolidCore.Solidity.Source.Stmt) (S : SymState) (b : Br), eraseSeq f ss S = some b → eraseSeq g ss S = some b
  | [], _, _, h => h
  | s :: rest, S, b, h => by
    simp only [eraseSeq, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨b0, h0, hb⟩ := h
    exact ⟨b0, hfg s S b0 h0, Br.bind_mono (fun S' r hr => eraseSeq_mono hfg rest S' r hr) hb⟩

/-- **An erasure that finishes at fuel `n` is the same at every `m ≥ n`.** -/
theorem eraseStmt_mono (E : EraseEnv) : ∀ (n m : Nat), n ≤ m →
    ∀ (s : SolidCore.Solidity.Source.Stmt) (S : SymState) (b : Br), eraseStmt E n s S = some b → eraseStmt E m s S = some b
  | 0, _, _, _, _, _, h => by simp [eraseStmt] at h
  | n + 1, 0, hnm, _, _, _, _ => absurd hnm (by omega)
  | n + 1, m + 1, hnm, s, S, b, h => by
    have ih : ∀ s S b, eraseStmt E n s S = some b → eraseStmt E m s S = some b :=
      eraseStmt_mono E n m (by omega)
    unfold eraseStmt at h ⊢
    split at h
    all_goals (try dsimp only)
    all_goals (try exact h)
    all_goals (try (simp at h; done))
    case h_2 =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨b0, h0, hb⟩ := h
      exact ⟨b0, eraseSeq_mono ih _ _ _ h0, hb⟩
    case h_9 =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨gs, v⟩, hp, h⟩ := h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨bt, ht, be, he, hb⟩ := h
      exact ⟨⟨gs, v⟩, hp, by
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
        exact ⟨bt, ih _ _ _ ht, be, ih _ _ _ he, hb⟩⟩
    case h_15 =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨fn, hfn, h⟩ := h
      refine ⟨fn, hfn, ?_⟩
      split at h
      · rename_i hc
        rw [if_pos hc]
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨⟨gs, vs⟩, hp, h⟩ := h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨b0, h0, b1, h1, hb⟩ := h
        exact ⟨⟨gs, vs⟩, hp, by
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
          exact ⟨b0, ih _ _ _ h0, b1, h1, hb⟩⟩
      · simp at h
    case h_16 =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨b0, h0, hb⟩ := h
      exact ⟨b0, ih _ _ _ h0, hb⟩

/-- **An erased function's tree at fuel `n` is its tree at every `m ≥ n`.** -/
theorem eraseFn_mono {E : EraseEnv} {n m : Nat} (hnm : n ≤ m) {fn : Source.FunctionDef} {T : Tree}
    (h : eraseFn E n fn = some T) : eraseFn E m fn = some T := by
  unfold eraseFn at h ⊢
  split at h
  · simp at h
  split at h
  case isFalse => simp at h
  rename_i hret
  rw [if_pos hret]
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨b, hb, t, ht, hT⟩ := h
  exact ⟨b, eraseStmt_mono _ n m hnm _ _ _ hb, t, ht, hT⟩

end Erase

/-! ## The generic source stage, uniformly from one fuel -/

/-- The constructor of `c` leaves the entries `s` and no logs at every fuel from `n` on. -/
def DeployStable (n : Nat) (c : TypeCheck.CheckedContract) (s : List (Nat × Nat)) : Prop :=
  ∀ m, n ≤ m → ∃ d, Wide.DeployedAt m c d s

/-- **Every function the generic source stage erases at `n` runs uniformly from `n`** on the
stage's scope, given that the constructor's result is stable from `n`. -/
theorem uniformFrom_stage {n : Nat} {c : TypeCheck.CheckedContract} {s : List (Nat × Nat)}
    (hdep : DeployStable n c s) {fn : Fn} {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) n f = some T) :
    UniformFrom n c (VC.stageScope fn s) := by
  rintro _ ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ m hnm
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨dm, hdm⟩ := hdep m hnm
  obtain ⟨dn, hdn⟩ := hdep n (Nat.le_refl n)
  rw [source_run hdm hcov hsel hfind (Erase.eraseFn_mono hnm hT) args (hl.trans hlen.symm) hargs,
    source_run hdn hcov hsel hfind hT args (hl.trans hlen.symm) hargs]

/-- **The generic theorem from an erased function to its obligations, at every fuel from `n`
on.** -/
theorem triple_of_binds_from {n m : Nat} (hnm : n ≤ m) {c : TypeCheck.CheckedContract}
    {s : List (Nat × Nat)} (hdep : DeployStable n c s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) n f = some T) {obs : List (List VC.Tm × VC.Tm)}
    {env : List Nat → Storage → VC.Env} {P : List Nat → Storage → Observable → Prop}
    (hobs : VC.ObsValid obs) (hbind : VC.Binds fn T obs env P) :
    Triple m c (VC.stageScope fn s) (fun _ => True) (VC.treePost fn P) := by
  obtain ⟨d, hd⟩ := hdep n (Nat.le_refl n)
  exact Triple.mono_of_uniform (uniformFrom_stage hdep hsel hfind hlen hT) hnm
    (VC.triple_of_binds hd hsel hfind hlen hT hobs hbind)

end SolidCore.Verify

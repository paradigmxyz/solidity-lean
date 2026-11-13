import Verify.Abi
import SolidCore.Refinement.Generic.SourceRun

/-!
# The generic source stage's trees as Loom models

The generic source stage (`SolidCore.Refinement.Generic`) erases a SolidCore function of its
fragment to a `Tree` (`eraseFn`) and proves that SolidCore runs every call of it as the tree
(`source_run`). `treeModel T` reads the tree as a model in `SolM`, the monad of
`SolidCore.Verify`'s Loom generator: it reads the storage, branches where the tree branches, and
ends as the tree's leaf does, writing the leaf's storage and returning its output, or reverting
with it. `implements_tree` is `Implements` for every function the stage erases, proved once from
`source_run`: so Loom's weakest precondition of `treeModel T` (`vc`, computed by `wp_bind`, `wp_ite`
and the rules below) gives a `Triple` against `Source.run` through `triple_of_wp`, with no proof
per contract of how SolidCore runs it.

The scope is the stage's: every call of the function on any argument words below `2 ^ 256`, with
no value, from any storage that writes every slot the constructor wrote (`Covers`). A model emits
no logs (`observe`), so the tree must have none (`noLogs`).
-/

namespace SolidCore.Verify.VC

open SolidCore.Verify SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- Read the whole storage. -/
def getStore : SolM Storage := fun s => .ok (s, s)

/-- Replace the whole storage. -/
def setStore (s' : Storage) : SolM Unit := fun _ => .ok ((), s')

@[simp] theorem wp_getStore (post : Storage → Assn) :
    wp getStore post = fun herr s => post s herr s := by
  rw [wp_eq]; rfl

@[simp] theorem wp_setStore (s' : Storage) (post : Unit → Assn) :
    wp (setStore s') post = fun herr _ => post () herr s' := by
  rw [wp_eq]; rfl

/-- The words of a call on the argument words `args` from the storage `s`, with SolidCore's slot
hash. -/
def valOf (args : List Nat) (s : Storage) : Val := ⟨args, s, solHash⟩

/-- A tree that emits no log. -/
def noLogs : Tree → Bool
  | .halt _ _ _ ls => ls.isEmpty
  | .ite _ t e => noLogs t && noLogs e

/-- The tree as a model: branch on the words of the call, end as the leaf does. -/
def treeModel : Tree → List Nat → SolM (List Nat)
  | .halt ok out ws _, args => do
    let s ← getStore
    if ok then do
      setStore (Writes.store (valOf args s) ws)
      pure (out.map (OByte.eval (valOf args s)))
    else revert (out.map (OByte.eval (valOf args s)))
  | .ite c t e, args => do
    let s ← getStore
    if c.eval (valOf args s) = 0 then treeModel e args else treeModel t args

/-- What a tree's result is as a model's outcome. -/
def resOutcome (R : Res) : Except Revert (List Nat × Storage) :=
  if R.success then .ok (R.output, R.store) else .error R.output

theorem treeModel_run (args : List Nat) (s : Storage) :
    ∀ T : Tree, treeModel T args s = resOutcome (T.eval (valOf args s))
  | .halt ok out ws ls => by
    cases ok <;> rfl
  | .ite c t e => by
    show (if c.eval (valOf args s) = 0 then treeModel e args else treeModel t args) s = _
    simp only [Tree.eval]
    split
    · exact treeModel_run args s e
    · exact treeModel_run args s t

theorem eval_logs (ρ : Val) : ∀ T : Tree, noLogs T = true → (T.eval ρ).logs = []
  | .halt ok out ws ls, h => by
    simp only [noLogs, List.isEmpty_iff] at h
    subst h; cases ok <;> rfl
  | .ite c t e, h => by
    simp only [noLogs, Bool.and_eq_true] at h
    simp only [Tree.eval]
    split
    · exact eval_logs ρ e h.2
    · exact eval_logs ρ t h.1

theorem observe_resOutcome (s : Storage) (R : Res) (hs : R.success = false → R.store = s)
    (hl : R.logs = []) : observe s (resOutcome R) = R.obs := by
  unfold resOutcome observe Res.obs
  cases h : R.success
  · simp [hs h, hl]
  · simp [hl]

theorem eval_store_fail (ρ : Val) : ∀ T : Tree, (T.eval ρ).success = false →
    (T.eval ρ).store = ρ.store
  | .halt ok out ws ls, h => by cases ok <;> simp_all [Tree.eval]
  | .ite c t e, h => by
    simp only [Tree.eval] at h ⊢
    split at h <;> rename_i hc <;> simp only [hc, ite_true, ite_false] <;>
      first | exact eval_store_fail ρ e h | exact eval_store_fail ρ t h

/-- The stage's scope of one function: every call of it on argument words below `2 ^ 256`, with no
value, from any storage that writes every slot the constructor wrote. -/
def stageScope (fn : Fn) (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ σ, Covers s σ ∧ fullScope [fn] σ call

/-- Every function the generic source stage erases is implemented by its tree's model. -/
theorem implements_tree {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) (hlogs : noLogs T = true) :
    Implements fuel c (stageScope fn s) (argWords fn.params.length) (treeModel T) := by
  rintro _ ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  have hw : argWords fn'.params.length
      ({ calldata := Abi.calldata fn'.sel args, callvalue := 0, storage := σ } : Call) = args :=
    hl ▸ argWords_calldata _ args hargs 0 σ
  rw [hw, source_run hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs]
  simp only [initStorage]
  rw [treeModel_run]
  exact congrArg some (observe_resOutcome _ _ (eval_store_fail _ T)
    (eval_logs _ T hlogs)).symm

end SolidCore.Verify.VC

import Verify.Spec.Tree
import Verify.ShapeSpecExport

/-!
# The ghost step solar-verify's export defines

A spec with ghost variables means something only with the ghost code that updates them: an
invariant such as `totalSupply == sumBalances` holds after `mint` with `sumBalances` increased by the
amount, not with it unchanged. The export lists each function's ghost assignments
(`FnSpec.ghostSets`), and this module reads the ghost step from them:

* `FnSpec.ghostPost`: the ghost state after a call of the function, its assignments run in order,
  each right side evaluated in the call's environment over the ghost state so far (the storage the
  call starts from, the block's timestamp);
* `Bundle.ghostStep`: the ghost step of the whole contract: a call runs the ghost assignments of the
  function spec of its selector on its decoded arguments, and any other call changes nothing;
* `Bundle.ghostStep_eq_of`: for an export with no ghost assignments, the ghost step is the identity,
  so a statement stated with it is the statement with `Shapes.idStep`.
* `TreeMeetsGhost` and `holdsFn_of_tree_ghost`: a function's spec from its erased tree with the
  ghost state its own assignments leave, the statement a function with ghost code needs.
-/

namespace SolidCore.Spec

open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- The ghost state after a call of `fs` on the arguments `args` from the storage `st` and the ghost
state `g`: its ghost assignments in order. -/
noncomputable def FnSpec.ghostPost (b : Bundle) (fs : FnSpec) (ctx : Ctx) (args : List Int)
    (st : Storage) (g : Ghost) : Ghost :=
  fs.ghostSets.foldl (fun g a =>
    let e := mkEnv ctx args [] ⟨st, g, ctx.timestamp⟩ ⟨st, g, ctx.timestamp⟩
    let kv := evalList b.spec.fns b.fuel a.2.1 e
    let v := eval b.spec.fns b.fuel a.2.2 e
    fun y ks => if y = a.1 ∧ ks = kv then v else g y ks) g

/-- A function without ghost assignments leaves the ghost state alone. -/
theorem FnSpec.ghostPost_nil {b : Bundle} {fs : FnSpec} (h : fs.ghostSets = []) (ctx : Ctx)
    (args : List Int) (st : Storage) (g : Ghost) : fs.ghostPost b ctx args st g = g := by
  simp [FnSpec.ghostPost, h]

/-- The function spec of a call's selector. -/
def Bundle.specOf (b : Bundle) (call : Call) : Option FnSpec :=
  b.spec.specs.find? fun fs => fs.selector == selectorOf call

/-- **The contract's ghost step**: a call runs the ghost assignments of the function spec of its
selector on its decoded arguments; a call no spec decodes changes nothing. -/
noncomputable def Bundle.ghostStep (b : Bundle) (ctxOf : Call → Ctx) : GhostStep := fun call g =>
  match b.specOf call with
  | none => g
  | some fs =>
    match decodeWords fs.params (words ((call.calldata.data.toList.map (·.toNat)).drop 4)) with
    | none => g
    | some args => fs.ghostPost b (ctxOf call) args (slotValue call.storage) g

/-- **With no ghost assignments, the contract's ghost step is the identity**: checked of an export by
the kernel's evaluation of `h`. -/
theorem Bundle.ghostStep_eq_of (b : Bundle) (ctxOf : Call → Ctx)
    (h : (b.spec.specs.all fun fs => fs.ghostSets.isEmpty) = true) (call : Call) (g : Ghost) :
    b.ghostStep ctxOf call g = g := by
  unfold Bundle.ghostStep
  split
  · rfl
  · rename_i fs hfs
    have hm := List.mem_of_find?_eq_some hfs
    have he := List.all_eq_true.mp h fs hm
    split
    · rfl
    · exact FnSpec.ghostPost_nil (List.isEmpty_iff.mp he) _ _ _ _

/-- What a function's spec asks of its erased tree when the call leaves the ghost state its own
ghost assignments compute: `TreeMeetsFixed` with `FnSpec.ghostPost` for the post-state's ghost state. -/
def TreeMeetsGhost (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) : Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ a ∈ args, a < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    Post b fs ctx pre (fs.ghostPost b ctx iargs s pre.ghost)
      (T.eval ⟨args, s, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs iargs

/-- On a call of the stage's scope of `fn` whose selector's spec is `fs`, the contract's ghost step
is `fs`'s ghost assignments on the call's arguments. -/
theorem ghostStep_of_scope {b : Bundle} {ctxOf : Call → Ctx} {fn : Fn} {s : List (Nat × Nat)}
    {fs : FnSpec} (hsel : fn.sel < 2 ^ 32)
    (hfind : b.spec.specs.find? (fun fs => fs.selector == fn.sel) = some fs)
    {call : Call} (hcall : SolidCore.Verify.VC.stageScope fn s call) {args : List Int}
    (hdec : Decodes fs call args) (g : Ghost) :
    b.ghostStep ctxOf call g = fs.ghostPost b (ctxOf call) args (slotValue call.storage) g := by
  obtain ⟨σ, -, fn', hfn', ws, -, -, rfl⟩ := hcall
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨-, -, hd⟩ := hdec
  have hs : selectorOf { calldata := calldata fn'.sel ws, callvalue := 0, storage := σ } = fn'.sel :=
    SolidCore.Refinement.Shapes.selectorOf_calldata hsel ws 0 σ
  unfold Bundle.ghostStep Bundle.specOf
  rw [hs, hfind]
  simp only
  rw [hd]


/-- **A function's spec with its own ghost assignments holds of SolidCore's contract when it holds
of the erased tree** (`TreeMeetsGhost`), on the stage's calls of the function, with the contract's
ghost step: `holdsFn_of_tree_fixed` for a function with ghost code. `hspec`, that `fs` is the first
spec of the function's selector, is the kernel's evaluation of the export. -/
theorem holdsFn_of_tree_ghost {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hspec : b.spec.specs.find? (fun fs' => fs'.selector == fn.sel) = some fs)
    (hm : TreeMeetsGhost b fs ctx fn.params.length T) :
    HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf (b.ghostStep ctxOf) fs := by
  intro call hcall iargs pre hpre
  have hstep := ghostStep_of_scope (ctxOf := ctxOf) hsel hspec hcall hpre.1 pre.ghost
  obtain ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ := hcall
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hctx _ rfl] at ht hreq hinv hstep ⊢
  rw [words_calldata _ hargs] at hdec
  rw [hstep]
  exact ⟨_, source_run hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs,
    hm args (slotValue σ) iargs pre hl hargs (fun k => Generic.slotValue_lt σ k) hdec hst ht hreq hinv⟩

/-- info: 'SolidCore.Spec.holdsFn_of_tree_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_tree_ghost

/-- info: 'SolidCore.Spec.Bundle.ghostStep_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Bundle.ghostStep_eq_of

end SolidCore.Spec

namespace SolidCore.Refinement.Shapes

/-- **The ghost step the published statement names**: the export's (`Bundle.ghostStep`) in the
interface's frame. For an export with no ghost assignments it is `idStep` (`exportStep_eq_id`). -/
noncomputable def exportStep (b : SolidCore.Spec.Bundle) : SolidCore.Spec.GhostStep :=
  b.ghostStep ctxOfCall

theorem exportStep_eq_id {b : SolidCore.Spec.Bundle}
    (h : (b.spec.specs.all fun fs => fs.ghostSets.isEmpty) = true) : exportStep b = idStep := by
  funext call g
  exact SolidCore.Spec.Bundle.ghostStep_eq_of b ctxOfCall h call g

end SolidCore.Refinement.Shapes

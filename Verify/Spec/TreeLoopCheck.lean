import Verify.Spec.TreeLoop
import Verify.LoopSource.Proof.EraseLoop

/-!
# The loop route's spec premises from one kernel check and `TreeMeets`

What `Verify.LoopSource.Equiv.LeastFuel.eraseLoop_certified` (and `eraseLoop_certified_loops`) take
of a one-loop function at selector `sel` besides the bytecode's side: SolidCore's function `f` of
the selector, its argument widths `ws`, word returns, the loop erasure `eraseLoopStmt` to some `br`,
`brTree` of it to `T`, and `OnTree` of the allowed statuses and the postcondition on `T`. For the
driver's specification (solar-verify's export, `Shapes.bundleAllowed` and `Shapes.bundlePost` at
`Shapes.ctxOfCall` and `Shapes.idStep`) this is `LoopSpec`.

* `contractLoopCheck`: a `Bool` the kernel evaluates (spec_connect.py's `F_loop_eq`, by
  `kernel_rfl`): the contract type checks, its function of `sel` has `n` parameters and widths
  `ws` and word returns, its loop erasure's tree is `T`, and the bundle `b` is the contract's
  export with its spec of `sel` at index `i` (`exportedCheck`);
* `loopSpec_of_check`: that check and `TreeMeets` (`loopSpec_of_check_fixed`: `TreeMeetsFixed`) of
  every function spec of the selector at `TreeLoop.ctx0` give `LoopSpec`;
* `not_loopSpec_of_none`, `not_loopSpec_empty`, `contractLoopCheck_nil`: a bundle with no spec
  of the selector, such as the empty one, gives no `LoopSpec` and fails the check, so `LoopSpec`
  is never the vacuous `OnTree` of a bundle that says nothing about the function.

**The bundle is the contract's.** `LoopSpec c … b` includes `ExportedFor c b sel`: `b` is named
for the checked contract and has a spec of `sel` named for `c`'s function of `sel`
(`Contract.function`, as `--emit-lean-spec` names them). That is a check of names and the selector
only: it does not see the clauses, so `b` with an ensures or an invariant removed passes it
(TreeLoopCounter.lean's `bump_loop_noEnsures_eq`, `bump_loop_noInv_eq`). What binds the clauses and
the checked AST to the source bytes is the module spec_connect.py writes: it states every theorem of
`spec := exported`, the literal solar-verify exported in that run from the bytes whose SHA-256 the
manifest records, with the kernel's `spec_is_fresh` (the spec module's bundle is `exported`) and
`source_is_fresh` (`contract?` is the type checker on the front end's AST of the same bytes); a bundle
with a clause removed is not `exported` (`TreeLoopCounter.noEnsures_ne`, `noInv_ne`).

The tree is the one the check names, so `TreeMeets` speaks of the erasure's own tree. The frame is
`TreeLoop`'s fixed one: sender `0x2000`, value 0, timestamp 1, self `0x1000`.
-/

namespace SolidCore.Spec.TreeLoop

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Solidity.Source
open SolidCore.Refinement.Generic.Loop Verify.LoopSource.Generic
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed ctxOfCall idStep)

/-- `f` has the argument widths `ws` and word returns, and its loop erasure's tree is `T`. -/
def loopCheck (E : EraseEnv) (fuel : Nat) (f : FunctionDef) (ws : List Nat) (T : Tree) : Bool :=
  widthsOf f.params f.paramAbiCleanups == some ws && f.returns.all wordBinding &&
    ((eraseLoopStmt { E with facts := argFacts ws 0 } fuel f.body (initState f)).bind
      (brTree f (argFacts ws 0)) == some T)

/-- `b` is the export of the contract named `cname` and its spec at index `i` is the only spec of
`sel`, exported for the function `f` (`cname.f`). -/
def exportedCheck (cname : String) (f : FunctionDef) (b : Bundle) (sel i : Nat) : Bool :=
  b.spec.name == cname && selOnly b sel i &&
    (b.spec.specs[i]?.map (·.name) == some (cname ++ "." ++ f.name))

/-- The contract type checks, its function of `sel` has `n` parameters and passes `loopCheck`, and
`b` is the contract's export with that function's spec at index `i`. -/
def contractLoopCheck (c? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract)
    (fuel sel n : Nat) (ws : List Nat) (T : Tree) (b : Bundle) (i : Nat) : Bool :=
  match c? with
  | .ok c =>
    match c.core.findFunctionBySelector? sel with
    | some f => f.params.length == n && loopCheck (envOf c.core) fuel f ws T &&
        exportedCheck c.decl.name f b sel i
    | none => false
  | .error _ => false

/-- **`b` is solar-verify's export for the checked contract `c`**: it is named for the contract, and
it has a spec of `sel`, named for `c`'s function of `sel`. -/
def ExportedFor (c : SolidCore.Solidity.TypeCheck.CheckedContract) (b : Bundle) (sel : Nat) : Prop :=
  b.spec.name = c.decl.name ∧ ∃ f, c.core.findFunctionBySelector? sel = some f ∧
    ∃ fs ∈ b.spec.specs, fs.selector = sel ∧ fs.name = c.decl.name ++ "." ++ f.name

/-- **What the loop route takes of a function's source and spec**: the function of `sel`, its
widths, word returns, its loop erasure and the erasure's tree `T`, with solar-verify's exported spec
`b` as allowed statuses and postcondition on `T`, and `b` the contract's export with a spec of
`sel` (`ExportedFor`). -/
def LoopSpec (c : SolidCore.Solidity.TypeCheck.CheckedContract) (fuel sel : Nat) (ws : List Nat)
    (T : Tree) (b : Bundle) : Prop :=
  ∃ (f : FunctionDef) (br : Br), c.core.findFunctionBySelector? sel = some f ∧
    widthsOf f.params f.paramAbiCleanups = some ws ∧ f.returns.all wordBinding = true ∧
    eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel f.body (initState f) = some br ∧
    brTree f (argFacts ws 0) br = some T ∧ f.params.length = ws.length ∧
    OnTree sel f ws T (bundleAllowed b ctxOfCall) ∧ OnTree sel f ws T (bundlePost b ctxOfCall idStep) ∧
    ExportedFor c b sel

theorem facts_of_check {c? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : c? = .ok c) {fuel sel n : Nat}
    {ws : List Nat} {T : Tree} {b : Bundle} {i : Nat} (h : contractLoopCheck c? fuel sel n ws T b i = true) :
    ∃ (f : FunctionDef) (br : Br), c.core.findFunctionBySelector? sel = some f ∧
      widthsOf f.params f.paramAbiCleanups = some ws ∧ f.returns.all wordBinding = true ∧
      eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel f.body (initState f) = some br ∧
      brTree f (argFacts ws 0) br = some T ∧ f.params.length = n ∧
      exportedCheck c.decl.name f b sel i = true := by
  subst hc
  simp only [contractLoopCheck] at h
  split at h
  · rename_i f hf
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hn, hl⟩, hx⟩ := h
    simp only [loopCheck, Bool.and_eq_true, beq_iff_eq] at hn hl
    obtain ⟨⟨hw, hret⟩, hT⟩ := hl
    cases hb : eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel f.body (initState f) with
    | none => rw [hb] at hT; cases hT
    | some br =>
      rw [hb] at hT
      exact ⟨f, br, hf, hw, hret, hb, hT, hn, hx⟩
  · cases h

/-- **The check binds the bundle to the contract** (`ExportedFor`). -/
theorem exportedFor_of_check {c : SolidCore.Solidity.TypeCheck.CheckedContract} {f : FunctionDef}
    {b : Bundle} {sel i : Nat} (hf : c.core.findFunctionBySelector? sel = some f)
    (h : exportedCheck c.decl.name f b sel i = true) : ExportedFor c b sel := by
  simp only [exportedCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hname, honly⟩, hfn⟩ := h
  obtain ⟨hi, hs⟩ := selOnly_get honly
  rw [List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at hfn
  exact ⟨hname, f, hf, _, List.getElem_mem hi, hs, hfn⟩

theorem length_of_widths : ∀ {ps : List BindingDecl} {cs : List AbiCleanup} {ws : List Nat},
    widthsOf ps cs = some ws → ps.length = ws.length := by
  intro ps
  induction ps with
  | nil =>
    intro cs ws h
    cases cs with
    | nil => simp only [widthsOf, Option.some.injEq] at h; subst h; rfl
    | cons _ _ => simp [widthsOf] at h
  | cons p ps ih =>
    intro cs ws h
    cases cs with
    | nil => simp [widthsOf] at h
    | cons x cs =>
      simp only [widthsOf] at h
      cases hp : paramWidth p x with
      | none => simp [hp] at h
      | some w =>
        cases hr : widthsOf ps cs with
        | none => simp [hp, hr] at h
        | some r =>
          simp [hp, hr] at h
          subst h
          simp [ih hr]

/-- **The loop route's spec premises from the kernel's check and `TreeMeets`.** -/
theorem loopSpec_of_check {c? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : c? = .ok c) {fuel sel n : Nat}
    {ws : List Nat} {T : Tree} {b : Bundle} {i : Nat} (hchk : contractLoopCheck c? fuel sel n ws T b i = true)
    (hsel : sel < 2 ^ 32) (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel → TreeMeets b fs ctx0 n T) :
    LoopSpec c fuel sel ws T b := by
  obtain ⟨f, br, hf, hw, hret, hb, hT, hn, hx⟩ := facts_of_check hc hchk
  subst hn
  obtain ⟨hA, hP⟩ := onTree_ctxOfCall (fn := f) (ws := ws) hsel hm
  exact ⟨f, br, hf, hw, hret, hb, hT, length_of_widths hw, hA, hP, exportedFor_of_check hf hx⟩

/-- The same from `TreeMeetsFixed`. -/
theorem loopSpec_of_check_fixed {c? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : c? = .ok c) {fuel sel n : Nat}
    {ws : List Nat} {T : Tree} {b : Bundle} {i : Nat} (hchk : contractLoopCheck c? fuel sel n ws T b i = true)
    (hsel : sel < 2 ^ 32) (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel → TreeMeetsFixed b fs ctx0 n T) :
    LoopSpec c fuel sel ws T b := by
  obtain ⟨f, br, hf, hw, hret, hb, hT, hn, hx⟩ := facts_of_check hc hchk
  subst hn
  obtain ⟨hA, hP⟩ := onTree_ctxOfCall_fixed (fn := f) (ws := ws) hsel hm
  exact ⟨f, br, hf, hw, hret, hb, hT, length_of_widths hw, hA, hP, exportedFor_of_check hf hx⟩

/-- **A bundle with no spec of the selector gives no `LoopSpec`.** -/
theorem not_loopSpec_of_none {c : SolidCore.Solidity.TypeCheck.CheckedContract} {fuel sel : Nat}
    {ws : List Nat} {T : Tree} {b : Bundle} (h : ∀ fs ∈ b.spec.specs, fs.selector ≠ sel) :
    ¬ LoopSpec c fuel sel ws T b := by
  rintro ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, fs, hfs, hs, -⟩
  exact h fs hfs hs

/-- **The empty bundle gives no `LoopSpec`**: `b` with its function specs removed, whatever else it
says. -/
theorem not_loopSpec_empty {c : SolidCore.Solidity.TypeCheck.CheckedContract} {fuel sel : Nat}
    {ws : List Nat} {T : Tree} (b : Bundle) :
    ¬ LoopSpec c fuel sel ws T { b with spec := { b.spec with specs := [] } } :=
  not_loopSpec_of_none (by simp)

/-- **The empty bundle fails the kernel's check**, whatever the contract, selector and index. -/
theorem contractLoopCheck_nil {c? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract}
    {fuel sel n : Nat} {ws : List Nat} {T : Tree} {b : Bundle} (h : b.spec.specs = []) (i : Nat) :
    contractLoopCheck c? fuel sel n ws T b i = false := by
  simp only [contractLoopCheck]
  split
  · split
    · simp [exportedCheck, selOnly_nil h]
    · rfl
  · rfl

end SolidCore.Spec.TreeLoop

/-- info: 'SolidCore.Spec.TreeLoop.loopSpec_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.loopSpec_of_check

/-- info: 'SolidCore.Spec.TreeLoop.loopSpec_of_check_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.loopSpec_of_check_fixed

/-- info: 'SolidCore.Spec.TreeLoop.not_loopSpec_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.not_loopSpec_empty

/-- info: 'SolidCore.Spec.TreeLoop.contractLoopCheck_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.contractLoopCheck_nil

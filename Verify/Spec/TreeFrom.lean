import Verify.Spec.TreeSucceeds
import Verify.AnyCaller.Context
import SolidCore.Refinement.Generic.Value

/-!
# A spec from the erased tree, for every caller and every value

`Tree.lean`'s `TreeMeets` and `TreeSucceeds` evaluate a function's tree with the constant caller
`Generic.callerWord` and read its spec in one fixed context, so `holdsFn_of_tree` speaks of calls sent
by `callerAddress` alone. Here the tree is the one `eraseFnSym` gives, with `msg.sender` the
symbolic word `WExpr.caller`, and the caller and the call's value are parameters:

* `TreeMeetsFixedAt a` and `TreeSucceedsAt a` are `TreeMeetsFixed` and `TreeSucceeds` with the tree
  evaluated for the caller `a`; `ctxAt a v` is `AnyCaller.ctxOfCallFrom a`'s context of a call
  with value `v`.
* `TreeMeetsFrom` asks `TreeMeetsFixedAt a` in `ctxAt a 0` of every account `a < 2 ^ 160` other
  than the contract, and `ValueRefuses` asks that no pre-state meets the succeeds-if conditions
  of a call with a value other than 0 (so a nonpayable function, which then reverts, owes nothing).
* `holdsFn_of_tree_from_zero` gives, from `TreeMeetsFrom` alone, the spec's `HoldsFn` against
  `solidCoreFrom a` in `ctxOfCallFrom a`, for every such `a`, on every call of the function with any
  argument words and no value, from any storage covering the deployed one.
* `holdsFn_of_tree_from` gives, from both, the same on every call with any value below `2 ^ 256`
  (`fullScopeValue`), for a nonpayable function.

Both are generic: one proof for every checked contract, deployed state, function and spec; what a
contract still owes is `TreeMeetsFrom` (and `ValueRefuses`) of its own tree and spec. The
contract's address (`0x1000`) and the block's timestamp (1) stay those of `ctxOfCallFrom`; a
payable function is outside this module (its value-carrying calls run its tree, not a revert).
-/

namespace SolidCore.Spec

open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity SolidCore.Verify.AnyCaller

/-- The context of a call sent by `a` with value `v`: `ctxOfCallFrom a`'s, by value. -/
def ctxAt (a v : Nat) : Ctx := { sender := a, value := v, timestamp := 1, self := 0x1000 }

theorem ctxOfCallFrom_eq_ctxAt (a : Nat) (call : Call) :
    ctxOfCallFrom a call = ctxAt a call.callvalue := rfl

/-- `TreeMeetsFixed` with the tree evaluated for the caller `a`. -/
def TreeMeetsFixedAt (a : Nat) (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) : Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ x ∈ args, x < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    Post b fs ctx pre pre.ghost (T.eval ⟨args, s, solHash, a⟩).obs iargs

/-- `TreeSucceeds` with the tree evaluated for the caller `a`. -/
def TreeSucceedsAt (a : Nat) (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) : Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ x ∈ args, x < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    b.satAll fs.succeedsIf (mkEnv ctx iargs [] pre pre) →
    (T.eval ⟨args, s, solHash, a⟩).obs.success = true

/-- The spec without its succeeds-if conditions and the conditions apart give the spec. -/
theorem treeMeetsFixedAt_of_succeeds {a : Nat} {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat}
    {T : Tree} (h0 : TreeMeetsFixedAt a b fs.noSucc ctx n T) (hs : TreeSucceedsAt a b fs ctx n T) :
    TreeMeetsFixedAt a b fs ctx n T := by
  intro args s iargs pre hl hargs hsl hdec hst ht hreq hinv
  obtain ⟨hok, -⟩ := h0 args s iargs pre hl hargs hsl hdec hst ht hreq hinv
  exact ⟨hok, fun _ hsat => hs args s iargs pre hl hargs hsl hdec hst ht hreq hinv hsat⟩

/-- **The spec holds of the tree from every caller**: every account below `2 ^ 160` other than the
contract, each in its own context, with no value. -/
def TreeMeetsFrom (b : Bundle) (fs : FnSpec) (n : Nat) (T : Tree) : Prop :=
  ∀ a, a < 2 ^ 160 → a ≠ selfAddress → TreeMeetsFixedAt a b fs (ctxAt a 0) n T

/-- No call with a value other than 0 meets the succeeds-if conditions, from any caller. -/
def ValueRefuses (b : Bundle) (fs : FnSpec) : Prop :=
  ∀ a v (iargs : List Int) (pre : State), v ≠ 0 → v < 2 ^ 256 → fs.succeedsIf ≠ [] →
    ¬ b.satAll fs.succeedsIf (mkEnv (ctxAt a v) iargs [] pre pre)

/-- The calls of one function with any argument words and no value, from any storage covering the
deployed entries `s`. -/
def zeroScope (fn : Fn) (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ σ, Covers s σ ∧ fullScopeValue [fn] σ 0 call

/-- The calls of one function with any argument words and any value below `2 ^ 256`, from any
storage covering the deployed entries `s`. -/
def valueScope (fn : Fn) (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ σ v, Covers s σ ∧ fullScopeValue [fn] σ v call

theorem zeroScope_valueScope {fn : Fn} {s : List (Nat × Nat)} {call : Call}
    (h : zeroScope fn s call) : valueScope fn s call :=
  let ⟨σ, hcov, hv⟩ := h
  ⟨σ, 0, hcov, hv⟩

/-- **A function's spec holds of SolidCore's run from every caller, on its calls without a
value**, when it holds of the symbolic-caller tree from every caller. -/
theorem holdsFn_of_tree_from_zero {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnSym (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {step : GhostStep} (hstep : ∀ call, zeroScope fn s call → ∀ g, step call g = g)
    (hm : TreeMeetsFrom b fs fn.params.length T) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      HoldsFn (solidCoreFrom a fuel) c (zeroScope fn s) b (ctxOfCallFrom a) step fs := by
  intro a ha hne call hcall iargs pre hpre
  have hg := hstep call hcall pre.ghost
  obtain ⟨σ, hcov, -, fn', hfn', args, hl, hargs, rfl⟩ := hcall
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hg]
  have hrun := source_run_from a ha hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
  rw [words_calldata _ hargs] at hdec
  exact ⟨_, hrun, hm a ha hne args (slotValue σ) iargs pre hl hargs
    (fun k => SolidCore.Refinement.Evm.Wide.slotValue_lt σ k) hdec hst ht hreq hinv⟩

/-- **A nonpayable function's spec holds of SolidCore's run from every caller, at every value**,
when it holds of the symbolic-caller tree from every caller and no value-carrying call meets its
succeeds-if conditions. -/
theorem holdsFn_of_tree_from {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnSym (envOf c.core) fuel f = some T) {ws : List Nat}
    (hw : widthsOf f.params f.paramAbiCleanups = some ws) (hpay : f.payable = false)
    {b : Bundle} {fs : FnSpec} {step : GhostStep}
    (hstep : ∀ call, valueScope fn s call → ∀ g, step call g = g)
    (hm : TreeMeetsFrom b fs fn.params.length T) (hv : ValueRefuses b fs) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      HoldsFn (solidCoreFrom a fuel) c (valueScope fn s) b (ctxOfCallFrom a) step fs := by
  intro a ha hne call hcall iargs pre hpre
  have hg := hstep call hcall pre.ghost
  obtain ⟨σ, v, hcov, hvlt, fn', hfn', args, hl, hargs, rfl⟩ := hcall
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hg]
  by_cases hv0 : v = 0
  · subst hv0
    have hrun := source_run_from a ha hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
    rw [words_calldata _ hargs] at hdec
    exact ⟨_, hrun, hm a ha hne args (slotValue σ) iargs pre hl hargs
      (fun k => SolidCore.Refinement.Evm.Wide.slotValue_lt σ k) hdec hst ht hreq hinv⟩
  · have hrun := source_run_value_from a hd hsel hfind hw hpay args (hl.trans hlen.symm) hargs
      hv0 hvlt σ
    refine ⟨_, hrun, ⟨fun hok => ?_, fun hne' hsat => ?_⟩⟩
    · simp [rejected] at hok
    · exact absurd hsat (hv a v iargs pre hv0 hvlt hne')

/-- info: 'SolidCore.Spec.holdsFn_of_tree_from_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_tree_from_zero

/-- info: 'SolidCore.Spec.holdsFn_of_tree_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_tree_from

end SolidCore.Spec

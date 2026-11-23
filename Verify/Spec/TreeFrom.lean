import Verify.Spec.TreeSucceeds
import Verify.AnyCaller.Context
import SolidCore.Refinement.Generic.Value
import Verify.Spec.HashScope

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

/-! ## Functions that read and write mappings: a finite hash footprint per call

A mapping stores `m[k]` at `keccak256(k . m)`, and keccak256 is not injective, so a spec of a
function that reads or writes mappings needs a premise about which of its slots differ. The global
premise is false for nested mappings (`not_nestedSlotsSeparated`, HashScope.lean). Here, as in
`holdsFnUnder_of_tree_fixed`, each call carries its own premise, and from every caller `a` it is:

* `footprintFrom a idx ms args`: the finite list of preimages `k . m` for the mapping slots `ms`
  and the keys `k` the call touches, the caller `a` and the address arguments at the positions
  `idx`; it has exactly `(idx.length + 1) * ms.length` entries (`footprintFrom_length`).
* `FootprintSep a idx ms args`: `ScopedSep` of that list, keccak256 injective on its entries with
  every image at least `2 ^ 128`. Nothing is asked of any other preimage.

The premise is a computational assumption on keccak256 of the call's own preimages, stated in the
theorem call by call: it is not proved, and no global hash premise is used.
-/

/-- `TreeMeetsFixedOn` with the tree evaluated for the caller `a`, on the argument words meeting `P`. -/
def TreeMeetsFixedOnAt (a : Nat) (P : List Nat → Prop) (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat)
    (T : Tree) : Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ x ∈ args, x < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) → P args →
    Post b fs ctx pre pre.ghost (T.eval ⟨args, s, solHash, a⟩).obs iargs

/-- **The hash footprint of a call sent by `a`**: the preimages `k . m` of the slots `m[k]` for
`m ∈ ms` and `k` the caller or an address argument at a position in `idx`. -/
def footprintFrom (a : Nat) (idx ms args : List Nat) : List (List Nat) :=
  mapScope (callKeys a idx args) ms

/-- `mapScope K ms` has one preimage per key and mapping slot. -/
theorem mapScope_length (K ms : List Nat) : (mapScope K ms).length = K.length * ms.length := by
  induction K with
  | nil => simp [mapScope]
  | cons k K ih =>
    simp only [mapScope, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul]; omega

/-- The footprint is finite, with one preimage per key and mapping slot. -/
theorem footprintFrom_length (a : Nat) (idx ms args : List Nat) :
    (footprintFrom a idx ms args).length = (idx.length + 1) * ms.length := by
  rw [footprintFrom, mapScope_length]; simp [callKeys]

/-- **The finite keccak256 premise of one call sent by `a`**: keccak256 injective, with images at
least `2 ^ 128`, on the call's footprint and nothing else. -/
def FootprintSep (a : Nat) (idx ms args : List Nat) : Prop := ScopedSep (footprintFrom a idx ms args)

/-- For `transfer(to, value)` of one balance mapping at `m` (key `to` at position 0), the premise
is `ScopedSep (transferFootprint m a to)`: two preimages. -/
theorem footprintSep_transfer {a m dst v : Nat} (hto : dst < 2 ^ 160) :
    FootprintSep a [0] [m] [dst, v] ↔ ScopedSep (transferFootprint m a dst) := by
  have : dst % 2 ^ 160 = dst := Nat.mod_eq_of_lt hto
  simp only [FootprintSep, footprintFrom, callKeys, mapScope, transferFootprint, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, this]

/-- **The spec holds of the tree from every caller on the calls whose footprint premise holds.** -/
def TreeMeetsFootprintFrom (idx ms : List Nat) (b : Bundle) (fs : FnSpec) (n : Nat) (T : Tree) : Prop :=
  ∀ a, a < 2 ^ 160 → a ≠ selfAddress → TreeMeetsFixedOnAt a (FootprintSep a idx ms) b fs (ctxAt a 0) n T

/-- **`holdsFn_of_tree_from_zero` under a per-caller, per-call premise `P a`** on the argument
words: the spec of SolidCore's run from every caller on the calls without a value whose words meet it. -/
theorem holdsFnUnder_of_tree_from_on_zero {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnSym (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {step : GhostStep} (hstep : ∀ call, zeroScope fn s call → ∀ g, step call g = g)
    {P : Nat → List Nat → Prop}
    (hm : ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      TreeMeetsFixedOnAt a (P a) b fs (ctxAt a 0) fn.params.length T) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      HoldsFnUnder (fun call => P a (callArgs call)) (solidCoreFrom a fuel) c (zeroScope fn s) b
        (ctxOfCallFrom a) step fs := by
  intro a ha hne call hcall hq iargs pre hpre
  have hg := hstep call hcall pre.ghost
  obtain ⟨σ, hcov, -, fn', hfn', args, hl, hargs, rfl⟩ := hcall
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hg]
  have hrun := source_run_from a ha hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
  rw [words_calldata _ hargs] at hdec
  simp only [callArgs] at hq
  rw [words_calldata _ hargs] at hq
  exact ⟨_, hrun, hm a ha hne args (slotValue σ) iargs pre hl hargs
    (fun k => SolidCore.Refinement.Evm.Wide.slotValue_lt σ k) hdec hst ht hreq hinv hq⟩

/-- **`holdsFn_of_tree_from` under a per-caller, per-call premise `P a`**: at every value, for a
nonpayable function whose value-carrying calls meet no succeeds-if conditions. -/
theorem holdsFnUnder_of_tree_from_on {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnSym (envOf c.core) fuel f = some T) {ws : List Nat}
    (hw : widthsOf f.params f.paramAbiCleanups = some ws) (hpay : f.payable = false)
    {b : Bundle} {fs : FnSpec} {step : GhostStep}
    (hstep : ∀ call, valueScope fn s call → ∀ g, step call g = g) {P : Nat → List Nat → Prop}
    (hm : ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      TreeMeetsFixedOnAt a (P a) b fs (ctxAt a 0) fn.params.length T)
    (hv : ValueRefuses b fs) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      HoldsFnUnder (fun call => P a (callArgs call)) (solidCoreFrom a fuel) c (valueScope fn s) b
        (ctxOfCallFrom a) step fs := by
  intro a ha hne call hcall hq iargs pre hpre
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
    simp only [callArgs] at hq
    rw [words_calldata _ hargs] at hq
    exact ⟨_, hrun, hm a ha hne args (slotValue σ) iargs pre hl hargs
      (fun k => SolidCore.Refinement.Evm.Wide.slotValue_lt σ k) hdec hst ht hreq hinv hq⟩
  · have hrun := source_run_value_from a hd hsel hfind hw hpay args (hl.trans hlen.symm) hargs
      hv0 hvlt σ
    refine ⟨_, hrun, ⟨fun hok => ?_, fun hne' hsat => ?_⟩⟩
    · simp [rejected] at hok
    · exact absurd hsat (hv a v iargs pre hv0 hvlt hne')

/-- **A function's spec of SolidCore's run from every caller, for functions that read and write
mappings, on every call without a value whose finite hash footprint is separated.** For every
account `a < 2 ^ 160` other than the contract and every call of the function sent by `a` with any
argument words, no value and any storage covering the deployed one, the spec holds of SolidCore's
run whenever keccak256 is injective, with images at least `2 ^ 128`, on the
`(idx.length + 1) * ms.length` preimages of that call's footprint (`FootprintSep a idx ms`). -/
theorem holdsFnUnder_of_tree_from_footprint_zero {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnSym (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {step : GhostStep} (hstep : ∀ call, zeroScope fn s call → ∀ g, step call g = g)
    {idx ms : List Nat} (hm : TreeMeetsFootprintFrom idx ms b fs fn.params.length T) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      HoldsFnUnder (fun call => FootprintSep a idx ms (callArgs call)) (solidCoreFrom a fuel) c
        (zeroScope fn s) b (ctxOfCallFrom a) step fs :=
  holdsFnUnder_of_tree_from_on_zero hd hsel hfind hlen hT hstep hm

/-- **The same at every value below `2 ^ 256`**, for a nonpayable function whose value-carrying
calls meet no succeeds-if conditions. -/
theorem holdsFnUnder_of_tree_from_footprint {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnSym (envOf c.core) fuel f = some T) {ws : List Nat}
    (hw : widthsOf f.params f.paramAbiCleanups = some ws) (hpay : f.payable = false)
    {b : Bundle} {fs : FnSpec} {step : GhostStep}
    (hstep : ∀ call, valueScope fn s call → ∀ g, step call g = g) {idx ms : List Nat}
    (hm : TreeMeetsFootprintFrom idx ms b fs fn.params.length T) (hv : ValueRefuses b fs) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      HoldsFnUnder (fun call => FootprintSep a idx ms (callArgs call)) (solidCoreFrom a fuel) c
        (valueScope fn s) b (ctxOfCallFrom a) step fs :=
  holdsFnUnder_of_tree_from_on hd hsel hfind hlen hT hw hpay hstep hm hv

/-- info: 'SolidCore.Spec.holdsFnUnder_of_tree_from_footprint_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFnUnder_of_tree_from_footprint_zero

/-- info: 'SolidCore.Spec.holdsFnUnder_of_tree_from_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFnUnder_of_tree_from_footprint

/-- info: 'SolidCore.Spec.footprintSep_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms footprintSep_transfer


end SolidCore.Spec

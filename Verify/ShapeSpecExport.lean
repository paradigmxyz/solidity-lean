import Verify.ShapeBundle
import Verify.ShapeGeneric
import Verify.Spec.Tree

/-!
# Allowed statuses and the whole valid scope from solar-verify's exported spec

The certify driver's strongest status reads both the postcondition and the allowed statuses off
solar-verify's export of the run's source, never off a Lean restatement:

* `bundlePost b ctxOf step` (`Verify.ShapeBundle`) is the postcondition;
* `bundleAllowed b ctxOf` is the allowed statuses: a call may revert only when no function spec
  whose precondition it meets has its succeeds-if conditions hold. A function spec with
  succeeds-if conditions says from which pre-states it must succeed, so a revert from such a
  pre-state is not allowed. A function without any makes no claim, as in solar-verify.

`allowed_of_holds` gives every source result's status from `SolidCore.Spec.Holds`, so the
published `Terminates` with `bundleAllowed` follows from the source's totality and the spec.

`holds_genericValid0` and `holds_genericValid` assemble `Holds` on the generic stage's valid
calls (`Shapes.genericValid0`, `Shapes.genericValid`) from each function spec's `HoldsFn` on the
stage's calls of the one function of its selector (`stageScope`, what
tools/certify/spec_connect.py proves for each function from its erased tree): a call of another
function has another selector, so no precondition of the spec holds of it; a call with a value of
a non-payable function reverts with empty data (`Generic.source_run_value`), which meets every
postcondition whose succeeds-if conditions require `msg.value == 0` (`valueGuarded`).

`ctxOfCall` and `idStep` are the call context and the ghost step the statement names: the
interface's one frame (sender `0x2000`, the contract at `0x1000`, block timestamp 1) with the call's
value, and no ghost update.
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Spec (Bundle FnSpec Pre Post HoldsFn Holds)

/-- The call context of the interface's one frame, with the call's value. -/
def ctxOfCall (call : Call) : SolidCore.Spec.Ctx :=
  { sender := 0x2000, value := call.callvalue, timestamp := 1, self := 0x1000 }

/-- No ghost update. -/
def idStep : SolidCore.Spec.GhostStep := fun _ g => g

/-- **The statuses solar-verify's exported spec allows**: success, or a call from which no
function spec with succeeds-if conditions must succeed. -/
def bundleAllowed (b : Bundle) (ctxOf : Call → SolidCore.Spec.Ctx) (call : Call)
    (obs : Observable) : Prop :=
  obs.success = true ∨ ∀ fs ∈ b.spec.specs, ∀ (args : List Int) (pre : SolidCore.Spec.State),
    Pre b fs (ctxOf call) pre call args → fs.succeedsIf ≠ [] →
      ¬ b.satAll fs.succeedsIf (SolidCore.Spec.mkEnv (ctxOf call) args [] pre pre)

/-- Every source result on a call of the spec's scope has an allowed status. -/
theorem allowed_of_holds {S : Sem} {p : S.Prog} {Valid scope : Call → Prop} {b : Bundle}
    {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep}
    (hv : ∀ call, Valid call → scope call) (h : Holds S p scope b ctxOf step) :
    ∀ call, Valid call → ∀ obs, S.run p call = some obs → bundleAllowed b ctxOf call obs := by
  intro call hc obs hrun
  by_cases hs : obs.success = true
  · exact Or.inl hs
  · refine Or.inr fun fs hfs args pre hpre hne hsat => hs ?_
    obtain ⟨obs', h1, h2⟩ := h fs hfs call (hv call hc) args pre hpre
    rw [hrun] at h1
    cases h1
    exact h2.2 hne hsat

/-- A specified compiled contract is certified with the exported spec's postcondition and allowed
statuses, from the spec's `Holds` of the source on a scope covering the valid calls. -/
theorem Compiled.certified_of_holds {S : Sem} {p : S.Prog} {code : ByteArray}
    {Valid scope : Call → Prop} {G : Call → Nat} {b : Bundle} {ctxOf : Call → SolidCore.Spec.Ctx}
    {step : SolidCore.Spec.GhostStep} (h : Compiled S p code Valid G)
    (hv : ∀ call, Valid call → scope call) (hh : Holds S p scope b ctxOf step) :
    Certified S p code Valid (bundleAllowed b ctxOf) (bundlePost b ctxOf step) G :=
  h.certified (allowed_of_holds hv hh) (meets_of_bundle hv hh)

/-! ## The selector of the stage's calls -/

theorem selectorOf_calldata {sel : Nat} (hsel : sel < 2 ^ 32) (args : List Nat) (v : Nat)
    (σ : List (Nat × Nat)) :
    SolidCore.Spec.selectorOf { calldata := calldata sel args, callvalue := v, storage := σ } = sel := by
  simp only [SolidCore.Spec.selectorOf]
  rw [Dirty.bytes_calldata, List.take_append_of_le_length (by simp [EthLib.Base.natToBytes_length]),
    List.take_of_length_le (by simp [EthLib.Base.natToBytes_length]), SolidCore.Spec.bytesWord_map,
    EthLib.Base.bytesToNat_natToBytes_of_lt (by simpa using hsel)]

/-- A function spec's precondition does not hold of a call of another selector. -/
theorem not_pre_of_sel {b : Bundle} {fs : FnSpec} {ctx : SolidCore.Spec.Ctx}
    {pre : SolidCore.Spec.State} {args : List Int} {sel : Nat} (hsel : sel < 2 ^ 32)
    (hne : sel ≠ fs.selector) (as : List Nat) (v : Nat) (σ : List (Nat × Nat)) :
    ¬ Pre b fs ctx pre { calldata := calldata sel as, callvalue := v, storage := σ } args := by
  rintro ⟨⟨-, hs, -⟩, -⟩
  rw [selectorOf_calldata hsel] at hs
  exact hne hs

/-- The stage's scope of a function depends on its selector and its number of parameters. -/
theorem stageScope_congr {fn fn' : Fn} (hs : fn.sel = fn'.sel)
    (hl : fn.params.length = fn'.params.length) (s : List (Nat × Nat)) (call : Call) :
    SolidCore.Verify.VC.stageScope fn s call → SolidCore.Verify.VC.stageScope fn' s call := by
  rintro ⟨σ, hcov, g, hg, args, hlen, hargs, rfl⟩
  simp only [List.mem_singleton] at hg
  subst hg
  exact ⟨σ, hcov, fn', List.mem_singleton_self _, args, hlen.trans hl, hargs, by rw [hs]⟩

/-- Whether every function of `fns` with the selector `sel` has `n` parameters, and every selector
of `fns` is below `2 ^ 32`: checked by the kernel's evaluation. -/
def selOk (fns : List Fn) (sel n : Nat) : Bool :=
  fns.all fun g => decide (g.sel < 2 ^ 32) && (g.sel != sel || g.params.length == n)

/-- **One function spec on the stage's calls without a value**, from its `HoldsFn` on the stage's
calls of the function of its selector. -/
theorem holdsFn_genericValid0 {S : Sem} {p : S.Prog} {fns : List Fn} {s : List (Nat × Nat)}
    {b : Bundle} {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep} {fs : FnSpec}
    {fn : Fn} (hfn : fn.sel = fs.selector) (hok : selOk fns fn.sel fn.params.length = true)
    (h : HoldsFn S p (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs) :
    HoldsFn S p (genericValid0 fns s) b ctxOf step fs := by
  rintro _ ⟨σ, hcov, g, hg, args, hlen, hargs, rfl⟩ iargs pre hpre
  have hk := List.all_eq_true.mp hok g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at hk
  obtain ⟨hlt, hk⟩ := hk
  by_cases he : g.sel = fn.sel
  · have hl := hk.resolve_left (not_not.mpr he)
    exact h _ (stageScope_congr he hl s _ ⟨σ, hcov, g, List.mem_singleton_self _, args, hlen, hargs,
      rfl⟩) iargs pre hpre
  · exact absurd hpre (not_pre_of_sel hlt (hfn ▸ he) args 0 σ)

/-- `Holds` from every function spec, by its index. -/
theorem holds_of_getElem {S : Sem} {p : S.Prog} {scope : Call → Prop} {b : Bundle}
    {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep}
    (h : ∀ i (hi : i < b.spec.specs.length), HoldsFn S p scope b ctxOf step b.spec.specs[i]) :
    Holds S p scope b ctxOf step := by
  intro fs hfs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfs
  exact h i hi

/-- info: 'SolidCore.Refinement.Shapes.Compiled.certified_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Compiled.certified_of_holds

/-- info: 'SolidCore.Refinement.Shapes.holdsFn_genericValid0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_genericValid0


/-! ## Calls with a value -/

/-- `msg.value == 0`, as solar-verify exports it. -/
def valueZero : SolidCore.Spec.Term := .bin .eq (.env .value) (.lit 0)

/-- The value guard: one of the spec's succeeds-if conditions is `msg.value == 0`, or a conjunction
`msg.value == 0 && e` (one condition, as solar-verify reads each condition on its own). -/
def valueGuarded (fs : FnSpec) : Prop :=
  ∃ t ∈ fs.succeedsIf, t = valueZero ∨ ∃ e, t = .bin .and valueZero e

theorem not_sat_of_value {b : Bundle} {fs : FnSpec} (hg : valueGuarded fs) {e : SolidCore.Spec.Env}
    (hv : e.ctx.value ≠ 0) : ¬ b.satAll fs.succeedsIf e := by
  intro h
  obtain ⟨t, ht, hgt⟩ := hg
  have := h t ht
  rcases hgt with rfl | ⟨x, rfl⟩ <;>
    simp [valueZero, SolidCore.Spec.Bundle.sat, SolidCore.Spec.eval, SolidCore.Spec.BinOp.apply,
      SolidCore.Spec.ofProp, hv] at this

/-- SolidCore rejects a value on every call of a function the generic check and the value check
accept. -/
theorem run_value {fuel mirFuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s)
    {m : SolarTV.MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true) {g : Fn} (hg : g ∈ fns)
    (args : List Nat) (hlen : args.length = g.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    {v : Nat} (hv0 : v ≠ 0) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    (solidCore fuel).run c { calldata := calldata g.sel args, callvalue := v, storage := σ } =
      some (rejected σ) := by
  have hcf := List.all_eq_true.mp hchk g hg
  have hcv := List.all_eq_true.mp hval g hg
  unfold Generic.checkFn at hcf
  unfold Generic.checkValueFn at hcv
  cases hfind : c.core.findFunctionBySelector? g.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : Generic.eraseFn (Generic.envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  simp only [hfind, ht1, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, -⟩ := hcf
  simp only [hfind, Bool.and_eq_true, Bool.not_eq_true'] at hcv
  obtain ⟨ws, hw⟩ := Generic.eraseFn_widths ht1
  exact Generic.source_run_value hd hsel hfind hw hcv.1 args (by rw [hlen, hpl]) hargs hv0 hv σ

/-- **One function spec on the stage's calls at every value**: the calls without a value from
its `HoldsFn` on the stage's calls of the function of its selector; the calls with a value revert
with empty data, which meets the spec when its succeeds-if conditions require `msg.value == 0`. -/
theorem holdsFn_genericValid {fuel mirFuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s)
    {m : SolarTV.MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {b : Bundle} {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep} {fs : FnSpec}
    (hctx : ∀ call, (ctxOf call).value = call.callvalue)
    (hguard : fs.succeedsIf = [] ∨ valueGuarded fs)
    {fn : Fn} (hfn : fn.sel = fs.selector) (hok : selOk fns fn.sel fn.params.length = true)
    (h : HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs) :
    HoldsFn (solidCore fuel) c (genericValid fns s) b ctxOf step fs := by
  rintro _ ⟨σ, v, hcov, hv, g, hg, args, hlen, hargs, rfl⟩ iargs pre hpre
  by_cases hv0 : v = 0
  · subst hv0
    exact holdsFn_genericValid0 hfn hok h _ ⟨σ, hcov, g, hg, args, hlen, hargs, rfl⟩ iargs pre hpre
  · refine ⟨_, run_value hd hchk hval hg args hlen hargs hv0 hv σ, fun hs => absurd hs (by
      simp [rejected]), fun hne hsat => absurd hsat (not_sat_of_value (hguard.resolve_left hne) ?_)⟩
    simp only [SolidCore.Spec.mkEnv, hctx]
    exact_mod_cast hv0

/-! ## Non-vacuity from a call whose succeeds-if conditions hold -/

/-- **Both non-vacuity witnesses from one valid call** from which a function spec with succeeds-if
conditions must succeed: the same call reverting is rejected by the exported postcondition and by
the exported allowed statuses. -/
theorem nonvacuous_of_succeeds {b : Bundle} {ctxOf : Call → SolidCore.Spec.Ctx}
    {step : SolidCore.Spec.GhostStep} {Valid : Call → Prop} {call : Call} (hc : Valid call)
    {fs : FnSpec} (hfs : fs ∈ b.spec.specs) {args : List Int} {pre : SolidCore.Spec.State}
    (hpre : Pre b fs (ctxOf call) pre call args) (hne : fs.succeedsIf ≠ [])
    (hsat : b.satAll fs.succeedsIf (SolidCore.Spec.mkEnv (ctxOf call) args [] pre pre)) :
    (∃ (call : Call) (obs : Observable), Valid call ∧ ¬ bundlePost b ctxOf step call obs) ∧
      (∃ (call : Call) (obs : Observable), Valid call ∧ obs.success = false ∧
        ¬ bundleAllowed b ctxOf call obs) := by
  let obs : Observable := ⟨false, [], [], slotValue call.storage⟩
  refine ⟨⟨call, obs, hc, fun h => ?_⟩, ⟨call, obs, hc, rfl, fun h => ?_⟩⟩
  · have := (h fs hfs args pre hpre).2 hne hsat
    cases this
  · rcases h with h | h
    · cases h
    · exact h fs hfs args pre hpre hne hsat

/-- A call of the stage's valid calls without a value: the function of `fns` with the selector
`sel` (found by evaluation) on zero words. -/
theorem valid0_of_find {fns : List Fn} {s σ : List (Nat × Nat)} (hcov : Generic.Covers s σ)
    {sel n : Nat} (h : (fns.find? (fun g => g.sel == sel)).map (·.params.length) = some n) :
    genericValid0 fns s { calldata := calldata sel (List.replicate n 0), callvalue := 0, storage := σ } := by
  cases hf : fns.find? (fun g => g.sel == sel) with
  | none => rw [hf] at h; cases h
  | some g =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hg := List.mem_of_find?_eq_some hf
    have hs := List.find?_some hf
    simp only [beq_iff_eq] at hs
    subst h hs
    exact ⟨σ, hcov, g, hg, List.replicate g.params.length 0, List.length_replicate,
      fun a ha => by rw [(List.mem_replicate.mp ha).2]; decide, rfl⟩

/-- The same call among the stage's valid calls at every value. -/
theorem valid_of_find {fns : List Fn} {s σ : List (Nat × Nat)} (hcov : Generic.Covers s σ)
    {sel n : Nat} (h : (fns.find? (fun g => g.sel == sel)).map (·.params.length) = some n) :
    genericValid fns s { calldata := calldata sel (List.replicate n 0), callvalue := 0, storage := σ } := by
  obtain ⟨σ', hc, hs⟩ := valid0_of_find hcov h
  exact ⟨σ', 0, hc, (Generic.fullScopeValue_zero _ _ _).2 hs⟩

/-- The precondition's decoding of the stage's call data on zero words. -/
theorem decodes_zero {fs : FnSpec} {sel n : Nat} (hsel : sel < 2 ^ 32) (hfs : fs.selector = sel)
    {args : List Int} (hd : SolidCore.Spec.decodeWords fs.params (List.replicate n 0) = some args)
    (v : Nat) (σ : List (Nat × Nat)) :
    SolidCore.Spec.Decodes fs { calldata := calldata sel (List.replicate n 0), callvalue := v, storage := σ } args := by
  refine ⟨?_, by rw [selectorOf_calldata hsel, hfs], ?_⟩
  · show 4 ≤ (calldata sel (List.replicate n 0)).size
    have := congrArg List.length (Dirty.bytes_calldata sel (List.replicate n 0))
    simp only [List.length_map, Array.length_toList, List.length_append, EthLib.Base.natToBytes_length] at this
    rw [ByteArray.size, this]
    omega
  · show SolidCore.Spec.decodeWords fs.params (SolidCore.Spec.words
      (((calldata sel (List.replicate n 0)).data.toList.map (·.toNat)).drop 4)) = some args
    rw [SolidCore.Spec.words_calldata _ (fun a ha => by rw [(List.mem_replicate.mp ha).2]; decide)]
    exact hd

/-- info: 'SolidCore.Refinement.Shapes.holdsFn_genericValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_genericValid

/-- info: 'SolidCore.Refinement.Shapes.nonvacuous_of_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonvacuous_of_succeeds


/-! ## A zero storage covering the constructor's slots -/

/-- The constructor's slots, each written with 0. -/
def zeros (s : List (Nat × Nat)) : List (Nat × Nat) := s.map fun kv => (kv.1, 0)

theorem covers_zeros (s : List (Nat × Nat)) : Generic.Covers s (zeros s) := by
  intro kv hkv
  exact ⟨(kv.1, 0), List.mem_map.mpr ⟨kv, hkv, rfl⟩, rfl⟩

theorem slotValue_zeros (s : List (Nat × Nat)) : slotValue (zeros s) = fun _ => 0 := by
  funext k
  unfold slotValue zeros
  suffices ∀ (l : List (Nat × Nat)) (a : Nat), a = 0 →
      (l.map fun kv => (kv.1, 0)).foldl (fun acc kv => if kv.1 % 2^256 = k % 2^256 then kv.2 % 2^256 else acc) a = 0 from
    this s 0 rfl
  intro l
  induction l with
  | nil => intro a h; simpa using h
  | cons x l ih =>
    intro a h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    split <;> simp [h]

end SolidCore.Refinement.Shapes

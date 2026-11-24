import Verify.LoopSource.Equiv.WithinFrom
import Verify.ShapeCtxGas

/-!
# The assembly theorems from any caller, from a loop invariant and a variant

`forward_of_checkXLFrom` and `within_of_checkXLFrom` take a block count `n` and a run of SolarTV's
EVM IR that ends within `n` blocks. Here the count comes from a loop invariant and a variant
instead of a run unrolled to a fixed fuel, so the theorems hold for every number of iterations:

* `Variant step Inv μ`: from every configuration where `Inv` holds the step is defined and either
  ends or continues to a configuration where `Inv` holds and `μ` is lower. `VariantWF` is the same
  with any well-founded order for the variant.
* `iterate_of_variant`: from a configuration where `Inv` holds the run ends within `μ x + 1` blocks;
  `iterate_of_variantWF`: with a well-founded order it ends.
* `forward_of_variantFrom`: at every gas from `gasBoundL cx.base (μ x₀ + 1)` on, where `x₀` is the
  entry configuration, EthLib runs the exact bytecode from the caller `a` to SolarTV's result. The
  gas is a premise of the theorem, as a function of the entry's variant; nothing bounds the
  iteration count.
* `within_of_variantFrom`: with a well-founded variant, at every gas every result of the bytecode
  is SolarTV's result or a failure that changes nothing. No gas premise.

Each takes the invariant on a program `q` whose runs are those of `guard F p` at every fuel (`hq`),
so it applies to the final EVM IR before guarding and normalizing; `q := guard F p` with `rfl` is
the direct case.

`forward_of_checkXLFrom` is a corollary (`forward_of_checkXLFrom_of_variant`): every run that ends
within `n` blocks has a variant, the least fuel at which it ends less one (`fuelMeasure`), whose
count is at most `n` (`fuelMeasure_le`), and `gasBoundL` is monotone in the count.
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolarTV SolarTV.Machine

section Iterate

variable {σ : Type}

/-- **A loop invariant with a variant**: from every configuration where `Inv` holds the step is
defined, and either ends or continues to a configuration where `Inv` holds and `μ` is lower. -/
def Variant (step : σ → Option ((Halt × State) ⊕ σ)) (Inv : σ → Prop) (μ : σ → Nat) : Prop :=
  ∀ x, Inv x → ∃ y, step x = some y ∧ ∀ x', y = .inr x' → Inv x' ∧ μ x' < μ x

/-- **A loop invariant with a well-founded variant**: as `Variant`, with the order `R`. -/
def VariantWF (step : σ → Option ((Halt × State) ⊕ σ)) (Inv : σ → Prop) (R : σ → σ → Prop) : Prop :=
  ∀ x, Inv x → ∃ y, step x = some y ∧ ∀ x', y = .inr x' → Inv x' ∧ R x' x

/-- A variant into `Nat` is a well-founded variant for the order it induces. -/
theorem Variant.wf {step : σ → Option ((Halt × State) ⊕ σ)} {Inv : σ → Prop} {μ : σ → Nat}
    (hv : Variant step Inv μ) : VariantWF step Inv (InvImage (· < ·) μ) :=
  hv

theorem iterate_succ_inr {step : σ → Option ((Halt × State) ⊕ σ)} {x x' : σ}
    (h : step x = some (.inr x')) (k : Nat) : iterate step (k + 1) x = iterate step k x' := by
  simp [iterate, h]

theorem iterate_le {step : σ → Option ((Halt × State) ⊕ σ)} {n m : Nat} {x : σ} {r : Halt × State}
    (le : n ≤ m) (h : iterate step n x = some r) : iterate step m x = some r := by
  induction le with
  | refl => exact h
  | step _ ih => exact iterate_mono step _ x r ih

/-- Two runs that end end with the same result. -/
theorem iterate_det {step : σ → Option ((Halt × State) ⊕ σ)} {n m : Nat} {x : σ}
    {r r' : Halt × State} (h : iterate step n x = some r) (h' : iterate step m x = some r') :
    r = r' := by
  have e := iterate_le (Nat.le_max_left n m) h
  rw [iterate_le (Nat.le_max_right n m) h'] at e
  exact (Option.some.inj e).symm

theorem iterate_of_variant_lt {step : σ → Option ((Halt × State) ⊕ σ)} {Inv : σ → Prop}
    {μ : σ → Nat} (hv : Variant step Inv μ) :
    ∀ (n : Nat) (x : σ), Inv x → μ x < n → ∃ r, iterate step n x = some r
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, h => by
    obtain ⟨y, hy, hnext⟩ := hv x hx
    cases y with
    | inl r => exact ⟨r, by simp [iterate, hy]⟩
    | inr x' =>
      obtain ⟨hi, hlt⟩ := hnext x' rfl
      obtain ⟨r, hr⟩ := iterate_of_variant_lt hv n x' hi (by omega)
      exact ⟨r, by rw [iterate_succ_inr hy]; exact hr⟩

/-- **From an invariant and a variant, the run ends within `μ x + 1` steps**, for every `μ x`. -/
theorem iterate_of_variant {step : σ → Option ((Halt × State) ⊕ σ)} {Inv : σ → Prop}
    {μ : σ → Nat} (hv : Variant step Inv μ) {x : σ} (hx : Inv x) :
    ∃ r, iterate step (μ x + 1) x = some r :=
  iterate_of_variant_lt hv _ x hx (Nat.lt_succ_self _)

/-- **From an invariant and a well-founded variant, the run ends.** -/
theorem iterate_of_variantWF {step : σ → Option ((Halt × State) ⊕ σ)} {Inv : σ → Prop}
    {R : σ → σ → Prop} (hwf : WellFounded R) (hv : VariantWF step Inv R) :
    ∀ x, Inv x → ∃ n r, iterate step n x = some r := by
  intro x
  refine hwf.induction (C := fun x => Inv x → ∃ n r, iterate step n x = some r) x ?_
  intro x ih hx
  obtain ⟨y, hy, hnext⟩ := hv x hx
  cases y with
  | inl r => exact ⟨1, r, by simp [iterate, hy]⟩
  | inr x' =>
    obtain ⟨hi, hR⟩ := hnext x' rfl
    obtain ⟨n, r, hr⟩ := ih x' hR hi
    exact ⟨n + 1, r, by rw [iterate_succ_inr hy]; exact hr⟩

/-! ## Every run that ends has a variant -/

/-- The configurations from which the run ends. -/
def Ends (step : σ → Option ((Halt × State) ⊕ σ)) (x : σ) : Prop :=
  ∃ k, (iterate step (k + 1) x).isSome = true

open Classical in
/-- The least fuel at which the run from `x` ends, less one (`0` when it never ends). -/
noncomputable def fuelMeasure (step : σ → Option ((Halt × State) ⊕ σ)) (x : σ) : Nat :=
  if h : Ends step x then Nat.find h else 0

theorem fuelMeasure_of {step : σ → Option ((Halt × State) ⊕ σ)} {x : σ} (h : Ends step x) :
    fuelMeasure step x = Nat.find h := by
  unfold fuelMeasure
  rw [dite_eq_left_of_eq_true (eq_true h)]

/-- **Every run that ends has a variant**: `Ends` with `fuelMeasure`. -/
theorem variant_fuelMeasure (step : σ → Option ((Halt × State) ⊕ σ)) :
    Variant step (Ends step) (fuelMeasure step) := by
  classical
  intro x hx
  have hk := Nat.find_spec hx
  cases hs : step x with
  | none => simp [iterate, hs] at hk
  | some y =>
    refine ⟨y, rfl, fun x' hy => ?_⟩
    subst hy
    rw [iterate_succ_inr hs] at hk
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hx = j + 1 := by
      cases h : Nat.find hx with
      | zero => rw [h] at hk; simp [iterate] at hk
      | succ j => exact ⟨j, rfl⟩
    rw [hj] at hk
    have hx' : Ends step x' := ⟨j, hk⟩
    refine ⟨hx', ?_⟩
    rw [fuelMeasure_of hx, fuelMeasure_of hx', hj]
    exact Nat.lt_succ_of_le (Nat.find_min' hx' hk)

/-- A run that ends within `n` steps has its variant's count at most `n`. -/
theorem fuelMeasure_le {step : σ → Option ((Halt × State) ⊕ σ)} {n : Nat} {x : σ}
    {r : Halt × State} (h : iterate step n x = some r) :
    Ends step x ∧ fuelMeasure step x + 1 ≤ n := by
  classical
  cases n with
  | zero => simp [iterate] at h
  | succ k =>
    have hk : (iterate step (k + 1) x).isSome = true := by rw [h]; rfl
    have hE : Ends step x := ⟨k, hk⟩
    refine ⟨hE, ?_⟩
    rw [fuelMeasure_of hE]
    exact Nat.succ_le_succ (Nat.find_min' hE hk)

end Iterate

/-- `gasBoundL` is monotone in the block count. -/
theorem gasBoundL_mono (c : Assemble.Cert) {m n : Nat} (h : m ≤ n) :
    gasBoundL c m ≤ gasBoundL c n := by
  unfold gasBoundL
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h)) _

end SolidCore.Refinement.Solar.AssembleLoop

namespace SolidCore.Refinement.Solar.AssembleCtxGas

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCtx

/-- The entry configuration of a call. -/
abbrev entry (call : SolarTV.Call) : Nat × EVM.Stack × SolarTV.Machine.State :=
  (0, [], SolarTV.Machine.State.initial call)

/-- **The forward assembly theorem from any caller, from a loop invariant and a variant.** For
every account `a` but the contract's, every call whose entry satisfies a loop invariant `Inv` with
a variant `μ` of the EVM IR `q` (whose runs are those of `guard F p`), and every gas from
`gasBoundL cx.base (μ (entry call) + 1)` on: SolarTV's run of `guard F p` ends within
`μ (entry call) + 1` blocks, and EthLib runs the exact bytecode from `a` to its result. -/
theorem forward_of_variantFrom {F : List Nat} {p : Assemble.Program} {code : ByteArray}
    {cx : CtxCert} (hc : checkXL F p code cx = true) (a : Nat)
    (hAB : Target.address selfAddress ≠ Target.address a) (o : SolarTV.Machine.Oracle)
    (ho : cx.base.env = true → OracleOkAt a o)
    (he : cx.base.reads = true → EnvOk o ∧ Target.txEnvFrom a = Target.txEnv)
    (call : SolarTV.Call) {q : Assemble.Program}
    (hq : ∀ n, EVM.Program.run o q call n = EVM.Program.run o (guard F p) call n)
    {Inv : Nat × EVM.Stack × SolarTV.Machine.State → Prop}
    {μ : Nat × EVM.Stack × SolarTV.Machine.State → Nat}
    (hv : Variant (EVM.Program.block o call q) Inv μ) (h0 : Inv (entry call))
    {gas : Nat} (hg : gasBoundL cx.base (μ (entry call) + 1) ≤ gas) :
    ∃ r, EVM.Program.run o (guard F p) call (μ (entry call) + 1) = some r ∧
      Final.Target.runWithFrom a gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨r, hr⟩ := iterate_of_variant hv h0
  have hr' : EVM.Program.run o (guard F p) call (μ (entry call) + 1) = some r := by
    rw [← hq]; exact hr
  exact ⟨r, hr', forward_of_checkXLFrom hc a hAB o ho he call _ r hr' hg⟩

/-- **The backward assembly theorem from any caller, from a loop invariant and a well-founded
variant.** SolarTV's run of `guard F p` ends, and at every gas every result EthLib gives for the
exact bytecode from `a` is its result, or a failure that changes nothing. -/
theorem within_of_variantFrom {F : List Nat} {p : Assemble.Program} {code : ByteArray}
    {cx : CtxCert} (hc : checkXL F p code cx = true) (a : Nat)
    (hAB : Target.address selfAddress ≠ Target.address a) (o : SolarTV.Machine.Oracle)
    (ho : cx.base.env = true → OracleOkAt a o) (hreads : cx.base.reads = false)
    (call : SolarTV.Call) {q : Assemble.Program}
    (hq : ∀ n, EVM.Program.run o q call n = EVM.Program.run o (guard F p) call n)
    {Inv : Nat × EVM.Stack × SolarTV.Machine.State → Prop}
    {R : Nat × EVM.Stack × SolarTV.Machine.State → Nat × EVM.Stack × SolarTV.Machine.State → Prop}
    (hwf : WellFounded R) (hv : VariantWF (EVM.Program.block o call q) Inv R)
    (h0 : Inv (entry call)) :
    ∃ r, (∃ n, EVM.Program.run o (guard F p) call n = some r) ∧
      ∀ gas obs, Final.Target.runWithFrom a gas code call = some obs →
        obs = SolarTV.Machine.observe call r.2 r.1 ∨
          (obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = []) := by
  obtain ⟨n, r, hr⟩ := iterate_of_variantWF hwf hv _ h0
  have hr' : EVM.Program.run o (guard F p) call n = some r := by
    rw [← hq]; exact hr
  exact ⟨r, ⟨n, hr'⟩, fun gas obs hrun =>
    within_of_checkXLFrom hc a hAB o ho hreads call n r hr' gas obs hrun⟩

/-- **The bounded theorem is a corollary**: `forward_of_checkXLFrom`'s statement, from
`forward_of_variantFrom` with the variant every ending run has (`variant_fuelMeasure`). -/
theorem forward_of_checkXLFrom_of_variant {F : List Nat} {p : Assemble.Program} {code : ByteArray}
    {cx : CtxCert} (hc : checkXL F p code cx = true) (a : Nat)
    (hAB : Target.address selfAddress ≠ Target.address a) (o : SolarTV.Machine.Oracle)
    (ho : cx.base.env = true → OracleOkAt a o)
    (he : cx.base.reads = true → EnvOk o ∧ Target.txEnvFrom a = Target.txEnv)
    (call : SolarTV.Call) (n : Nat) (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call (guard F p)) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL cx.base n ≤ gas) :
    Final.Target.runWithFrom a gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨hE, hle⟩ := fuelMeasure_le hit
  obtain ⟨r', hr', hrun⟩ := forward_of_variantFrom hc a hAB o ho he call (q := guard F p)
    (fun _ => rfl) (variant_fuelMeasure _) hE (Nat.le_trans (gasBoundL_mono cx.base hle) hg)
  rw [iterate_det hit hr']
  exact hrun

end SolidCore.Refinement.Solar.AssembleCtxGas

/-- info: 'SolidCore.Refinement.Solar.AssembleLoop.iterate_of_variant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleLoop.iterate_of_variant

/-- info: 'SolidCore.Refinement.Solar.AssembleLoop.iterate_of_variantWF' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleLoop.iterate_of_variantWF

/-- info: 'SolidCore.Refinement.Solar.AssembleLoop.variant_fuelMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleLoop.variant_fuelMeasure

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_variantFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_variantFrom

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.within_of_variantFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.within_of_variantFrom

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXLFrom_of_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXLFrom_of_variant

import Contracts.UniswapV2.ERC20.Slice.Statement

/-!
# UniswapV2ERC20.transfer: the specification carried to the bytes through `Equiv`

E7 of docs/CERTIFICATION_TARGET.md: the slice's specification, proved of SolidCore's runs
(Statement.lean), transferred to the exact runtime bytes by the behavioural equivalence
`Shapes.Equiv` the backend stages and the byte binding deliver (E4 to E6, other lanes). Nothing
here assumes anything of the bytes beyond the hypotheses named in each statement.

* `meets_bytes` (any source, any spec): `Equiv` and `Meets` give, at every gas below `2 ^ 256`,
  every result of the bytes on a valid call meeting the spec, or an inert failure (`Inert`: no
  change, no log; running out of gas is one, so no more can be said without a gas bound);
* `meets_bytes_enough`: with `Resources` (E8) as well, every result of the bytes from the gas bound
  on meets the spec exactly;
* for the slice: `terminates` (SolidCore halts on every valid call, succeeding or reverting with
  one of SafeMath's two errors, `Allowed`), and `functional_of_equiv`, `certified_of`: given
  `Equiv` (and `Resources`) for some bytes `code` on `ValidIn`, the target's `Functional`
  (`Certified`) statement with `TargetPost`; `bytes_target`, `bytes_seq`, `bytes_bundle`: the
  three specifications on the bytes, each with its `Inert` alternative.

The binding of `code` to the bytes solar emits for the pinned port, and `Equiv` itself, are not
proved here: they are the named premises `heq` (E4 to E6) and `hres` (E8).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen

/-! ## The transfer lemma -/

/-- **`Meets` from the source to the bytes through `Equiv`.** -/
theorem meets_bytes {S : Sem} {p : S.Prog} {code : ByteArray} {V : Call → Prop}
    {P : Call → Observable → Prop} (heq : Equiv S p code V) (hm : Meets S p V P) (gas : Nat)
    (hg : gas < 2 ^ 256) (call : Call) (hc : V call) (obs : Observable)
    (hrun : Final.Target.runWith gas code call = some obs) : P call obs ∨ Inert call obs :=
  (heq gas hg call hc obs hrun).imp (hm call hc obs) id

/-- **With a gas bound, exactly**: from `G call` gas on, every result of the bytes meets `P`. -/
theorem meets_bytes_enough {S : Sem} {p : S.Prog} {code : ByteArray} {V : Call → Prop}
    {P : Call → Observable → Prop} {G : Call → Nat} (hres : Resources S p code V G) (hm : Meets S p V P)
    (call : Call) (hc : V call) (gas : Nat) (h1 : G call ≤ gas) (h2 : gas < 2 ^ 256) (obs : Observable)
    (hrun : Final.Target.runWith gas code call = some obs) : P call obs := by
  rw [(hres call hc).2 gas h1 h2] at hrun
  exact hm call hc obs hrun

/-- A specification no bytes can meet vacuously by an inert failure: `TargetPost` asks a revert for
SafeMath's revert data, so an inert result with other output does not meet it. -/
theorem inert_not_target : ¬ TargetPost call0 ⟨false, [], [], slotValue σ0⟩ := by
  intro h
  have := ((h σ0 1 0 rfl (by decide) (by decide)).2.2.2 rfl).2.2
  simp [errorData] at this

/-! ## The slice -/

/-- The statuses `transfer` may end with: success, or a revert with one of SafeMath's errors. -/
def Allowed (_call : Call) (obs : Observable) : Prop :=
  obs.success = true ∨ obs.output = errorData subMsg ∨ obs.output = errorData addMsg

/-- **SolidCore halts on every valid call**, with an allowed status. -/
theorem terminates {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Terminates (solidCore fuel) c ValidIn Allowed := by
  rintro _ ⟨⟨σ, dst, v, hcov, hto, hv, rfl⟩, -⟩
  refine ⟨_, run_tree hc hcov hto hv, ?_⟩
  have hs := fun k => Generic.slotValue_lt σ k
  by_cases hle : v ≤ slotValue σ (balKey caller)
  · by_cases hov : debit (slotValue σ) v (balKey dst) + v < 2 ^ 256
    · rw [res_ok hs hto hv hle hov]; exact Or.inl rfl
    · rw [res_add hs hto hv hle hov]; exact Or.inr (Or.inr rfl)
  · rw [res_sub hs hto hv hle]; exact Or.inr (Or.inl rfl)

/-- **The slice's functional statement, given `Equiv`** for bytes `code` on the valid calls. -/
theorem functional_of_equiv {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {code : ByteArray}
    (heq : Equiv (solidCore fuel) c code ValidIn) :
    Functional (solidCore fuel) c code ValidIn Allowed TargetPost :=
  ⟨valid_inhabited, heq, terminates hc, meets_target hc⟩

/-- **The slice's certified statement, given `Equiv` and `Resources`.** -/
theorem certified_of {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {code : ByteArray} {G : Call → Nat}
    (heq : Equiv (solidCore fuel) c code ValidIn) (hres : Resources (solidCore fuel) c code ValidIn G) :
    Certified (solidCore fuel) c code ValidIn Allowed TargetPost G :=
  ⟨valid_inhabited, heq, terminates hc, meets_target hc, hres⟩

/-- **`TargetPost` on the bytes**, at every gas, or an inert failure. -/
theorem bytes_target {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {code : ByteArray}
    (heq : Equiv (solidCore fuel) c code ValidIn) (gas : Nat) (hg : gas < 2 ^ 256) (call : Call)
    (hv : ValidIn call) (obs : Observable) (hrun : Final.Target.runWith gas code call = some obs) :
    TargetPost call obs ∨ Inert call obs :=
  meets_bytes heq (meets_target hc) gas hg call hv obs hrun

/-- **`SeqPost` on the bytes**: no hash premise on the calls, only in `Equiv`'s. -/
theorem bytes_seq {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {code : ByteArray}
    (heq : Equiv (solidCore fuel) c code (Valid deployed)) (gas : Nat) (hg : gas < 2 ^ 256) (call : Call)
    (hv : Valid deployed call) (obs : Observable) (hrun : Final.Target.runWith gas code call = some obs) :
    SeqPost call obs ∨ Inert call obs :=
  meets_bytes heq (meets_seq hc) gas hg call hv obs hrun

/-- **solar-verify's exported spec on the bytes.** -/
theorem bytes_bundle {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {code : ByteArray}
    (heq : Equiv (solidCore fuel) c code ValidIn) (gas : Nat) (hg : gas < 2 ^ 256) (call : Call)
    (hv : ValidIn call) (obs : Observable) (hrun : Final.Target.runWith gas code call = some obs) :
    bundlePost spec ctxOf idStep call obs ∨ Inert call obs :=
  meets_bytes heq (meets_bundle hc) gas hg call hv obs hrun

/-- **With `Resources`, `TargetPost` of the bytes exactly** from the gas bound on. -/
theorem bytes_target_enough {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {code : ByteArray} {G : Call → Nat}
    (hres : Resources (solidCore fuel) c code ValidIn G) (call : Call) (hv : ValidIn call) (gas : Nat)
    (h1 : G call ≤ gas) (h2 : gas < 2 ^ 256) (obs : Observable)
    (hrun : Final.Target.runWith gas code call = some obs) : TargetPost call obs :=
  meets_bytes_enough hres (meets_target hc) call hv gas h1 h2 obs hrun

end SolidCore.Spec.UniswapV2.ERC20.Slice

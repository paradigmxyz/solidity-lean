import Verify.VC.Check
import Verify.VC.Discharge

/-!
# solar-verify's loop obligations, with their SSA versions kept

`checkOb` (Verify/VC/Check.lean) compares an obligation of solar-verify's script with a Lean
obligation after renaming every constant `name@N` to `name` (`strip`). That is sound, but
across a loop it identifies distinct versions of one variable: in a loop obligation `count@17`
(the value before the loop) and `count@27` (the value at the loop head) both become `count`,
so the Lean obligation it can match says nothing about the loop. `checkObRaw` is the same check
without the renaming: the Lean obligation names solar-verify's constants as the script does.

`checkLoop cs obs` pairs each Lean obligation with the index of the `check-sat` it comes from,
so a generated module states which of solar-verify's obligations (initiation, consecution,
termination, exit) each Lean one is, and `checkLoop_sound` gives `ObsValid` of them from the
verdict `Valid cs`, which `dischargeScript` (Verify/VC/Discharge.lean) decides in the kernel
without a solver.
-/

namespace SolidCore.Verify.VC

/-- solar-verify's obligation `e` gives the Lean obligation `hs ⟹ φ`, names kept. -/
def checkObRaw (e hs : List Tm) (φ : Tm) : Bool :=
  match (inline e).reverse with
  | .app "not" [φ'] :: rhyps => φ'.beq φ && (flattenList rhyps).all (hypOk hs (leanVars hs φ))
  | _ => false

theorem checkObRaw_sound {e hs : List Tm} {φ : Tm} (h : checkObRaw e hs φ = true)
    (hv : ∀ σ, ¬ Sat σ e) (σ : Env) (hh : ∀ x ∈ hs, x.Holds σ) : φ.Holds σ := by
  have h2 := inline_sound hv
  unfold checkObRaw at h
  split at h
  · rename_i φ' rhyps hr
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hφ, hyps⟩ := h
    have he := Tm.eq_of_beq hφ
    subst he
    have hφV : ∀ x ∈ φ'.vars, x ∈ leanVars hs φ' := fun x hx => by
      simp only [leanVars, List.mem_append]; exact Or.inr hx
    apply Classical.byContradiction
    intro hn
    apply h2 (σ.restrict (leanVars hs φ'))
    intro t ht
    have ht' : t ∈ (Tm.app "not" [φ'] :: rhyps).reverse := by
      rw [← hr, List.reverse_reverse]; exact ht
    rw [List.mem_reverse] at ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · simp only [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp]
      intro hp
      exact hn ((holds_restrict hφV).mp hp)
    · exact flatten_holds t _ fun c hc =>
        hypOk_sound hh (hyps c (mem_flattenList ht' hc))
  · simp at h

/-- Each Lean obligation `(k, hs, φ)` is given by the script's obligation at index `k`, which is
not a probe. -/
def checkLoop (cs : List Cmd) (obs : List (Nat × List Tm × Tm)) : Bool :=
  obs.all fun o =>
    decide (o.1 < (obligations cs).length) &&
      !isProbe ((obligations cs).getD o.1 []) &&
      checkObRaw ((obligations cs).getD o.1 []) o.2.1 o.2.2

theorem checkLoop_sound {cs : List Cmd} {obs : List (Nat × List Tm × Tm)}
    (h : checkLoop cs obs = true) (hv : Valid cs) : ObsValid (obs.map (·.2)) := by
  intro o ho σ hh
  obtain ⟨⟨k, hs, φ⟩, hmem, rfl⟩ := List.mem_map.mp ho
  have hk := List.all_eq_true.mp h _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
  obtain ⟨⟨hlt, hp⟩, hc⟩ := hk
  have hmem' : (obligations cs).getD k [] ∈ obligations cs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  exact checkObRaw_sound hc (fun τ hτ => hv _ hmem' hp τ hτ) σ hh

/-- A checked Lean obligation holds wherever its facts do. -/
theorem ObsValid.get {obs : List (Nat × List Tm × Tm)} (h : ObsValid (obs.map (·.2)))
    {o : Nat × List Tm × Tm} (hm : o ∈ obs) (σ : Env)
    (hh : ∀ x ∈ o.2.1, x.Holds σ) : o.2.2.Holds σ :=
  h o.2 (List.mem_map.mpr ⟨_, hm, rfl⟩) σ hh

end SolidCore.Verify.VC

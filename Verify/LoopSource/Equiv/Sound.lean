import Verify.LoopSource.Equiv.Foot

/-!
# The cut-point run is sound

`cutRun_sound`: a cut-point run from a symbolic frame describes every machine frame that holds it.
Each end is an end the module reaches, and each arrival at the header is a frame the module
reaches with no call in progress, related to the arrival's symbolic frame, whose footprint holds.
This follows `symRun_sound` step for step (`symStep_sound`, `MirRun.lean`), with `frame_step` for
the footprint.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement.Generic

/-- Every end reached from `y` is reached from `x`. -/
def Leads {σ : Type} (step : σ → Option ((Halt × State) ⊕ σ)) (x y : σ) : Prop :=
  ∀ k r, iterate step k y = some r → ∃ k', iterate step k' x = some r

theorem Leads.refl {σ : Type} (step : σ → Option ((Halt × State) ⊕ σ)) (x : σ) : Leads step x x :=
  fun k r h => ⟨k, h⟩

theorem Leads.trans {σ : Type} {step : σ → Option ((Halt × State) ⊕ σ)} {x y z : σ}
    (h1 : Leads step x y) (h2 : Leads step y z) : Leads step x z := fun k r h => by
  obtain ⟨k1, hk1⟩ := h2 k r h
  exact h1 k1 r hk1

theorem Leads.step {σ : Type} {step : σ → Option ((Halt × State) ⊕ σ)} {x y : σ}
    (h : step x = some (.inr y)) : Leads step x y := fun k r hk =>
  ⟨k + 1, by rw [iterate_inr h]; exact hk⟩

/-- Two frames with the same next step lead to the same ends. -/
theorem Leads.same {σ : Type} {step : σ → Option ((Halt × State) ⊕ σ)} {x y : σ}
    (h : step x = step y) : Leads step x y := fun k _ hk => ⟨k, by cases k <;> simp_all [iterate]⟩

/-- **What a cut-point tree says of a machine frame `x`**, on the call's valuation `ρ`: an end
`x` reaches with the tree's observable, or a header frame `x` leads to, related to the arrival and
under its footprint, on the side of each branch the valuation takes. -/
def CSound (ρ : Val) (call : Call) (o : Oracle) (m : Module) (fn head : Nat) (x : SolarTV.MIR.Lowered.Frame) :
    CTree → Prop
  | .done T => ∃ k r, iterate (moduleBlock o call m) k x = some r ∧ observe call r.2 r.1 = (T.eval ρ).obs
  | .back pred senv st D MO => ∃ env s, Leads (moduleBlock o call m) x ([], .enter fn pred head, env, s) ∧
      EnvRel ρ call env senv ∧ StRel ρ s st ∧ Frame D MO senv st
  | .ite e t f => if e.eval ρ = 0 then CSound ρ call o m fn head x f else CSound ρ call o m fn head x t

theorem CSound.pre {ρ : Val} {call : Call} {o : Oracle} {m : Module} {fn head : Nat} {x y : SolarTV.MIR.Lowered.Frame}
    (hxy : Leads (moduleBlock o call m) x y) : ∀ t : CTree, CSound ρ call o m fn head y t → CSound ρ call o m fn head x t
  | .done T, ⟨k, r, hk, hr⟩ => (hxy k r hk).imp fun _ hk' => ⟨r, hk', hr⟩
  | .back pred senv st D MO, ⟨env, s, hl, rest⟩ => ⟨env, s, hxy.trans hl, rest⟩
  | .ite e t f, h => by
    by_cases h0 : e.eval ρ = 0 <;> simp only [CSound, h0, ↓reduceIte] at h ⊢ <;> exact CSound.pre hxy _ h

theorem atHead_some {fn head : Nat} {pos : Pos} {pred : Nat} (h : atHead fn head pos = some pred) :
    pos = .enter fn pred head := by
  cases pos <;> simp only [atHead, Option.ite_none_right_eq_some, Option.some.injEq, reduceCtorEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

theorem stackRel_nil {ρ : Val} {call : Call} {ms : List Return} (h : StackRel ρ call ms []) : ms = [] := by
  cases ms <;> simp_all [StackRel]

/-- **The cut-point run is sound.** -/
theorem cutRun_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (henv : EnvAsk ev o ρ) (m : Module) (fn head : Nat) :
    ∀ (fuel : Nat) (pos : Pos) (senv : SEnv) (st : SState) (K : Facts) (D MO : List Nat) (t : CTree),
      cutRun ev cv m sel n fn head fuel pos senv st K D MO = some t →
      ∀ env s, EnvRel ρ call env senv → StRel ρ s st → K.Hold ρ → Frame D MO senv st →
      CSound ρ call o m fn head ([], pos, env, s) t
  | 0, _, _, _, _, _, _, _, h, _, _, _, _, _, _ => by simp [cutRun] at h
  | fuel + 1, pos, senv, st, K, D, MO, t, h, env, s, he, hs, hK, hF => by
    simp only [cutRun] at h
    cases hat : atHead fn head pos with
    | some pred =>
      simp only [hat, Option.some.injEq] at h
      subst h
      rw [atHead_some hat]
      exact ⟨env, s, Leads.refl _ _, he, hs, hF⟩
    | none =>
    cases hsf : stepFoot m pos with
    | none => simp [hat, hsf] at h
    | some dm =>
    obtain ⟨d, mo⟩ := dm
    cases hx : symStep ev cv m sel n K [] pos senv st with
    | none => simp [hat, hsf, hx] at h
    | some x =>
    have hn := symStep_sound hc henv m hK hx (ms := []) trivial he hs
    have hfr := frame_step hF hsf hx
    simp only [hat, hsf, hx] at h
    cases x with
    | done T =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨r, hr, hobs⟩ := hn
      exact ⟨1, r, iterate_inl hr, hobs⟩
    | go stack pos' senv' st' =>
      obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
      cases stack with
      | cons _ _ => simp at h
      | nil =>
      obtain rfl := stackRel_nil hst'
      exact CSound.pre (Leads.step hr) t
        (cutRun_sound hc o henv m fn head fuel pos' senv' st' K _ _ t h env' s' he' hs' hK (hfr rfl))
    | fork e stack fn' b yes no senv' st' =>
      obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
      cases stack with
      | cons _ _ => simp at h
      | nil =>
      obtain rfl := stackRel_nil hst'
      cases hdec : K.lookup e with
      | some bb =>
        -- the facts decide the branch
        have hv := Facts.lookup_sound hK hdec
        cases bb <;> simp only [hdec, hv, reduceCtorEq, ↓reduceIte] at h hr <;>
          exact CSound.pre (Leads.step hr) t
            (cutRun_sound hc o henv m fn head fuel _ senv' st' K _ _ t h env' s' he' hs' hK (hfr rfl))
      | none =>
      -- both sides, each under the fact that takes it
      simp only [hdec] at h
      split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      rename_i tt ff ht hf
      subst h
      by_cases h0 : e.eval ρ = 0 <;> simp only [CSound, h0, ↓reduceIte] at hr ⊢
      · exact CSound.pre (Leads.step hr) ff
          (cutRun_sound hc o henv m fn head fuel _ senv' st' _ _ _ ff hf env' s' he' hs'
            (hK.add e false (by simp [h0])) (hfr rfl))
      · exact CSound.pre (Leads.step hr) tt
          (cutRun_sound hc o henv m fn head fuel _ senv' st' _ _ _ tt ht env' s' he' hs'
            (hK.add e true (by simp [h0])) (hfr rfl))

end Verify.LoopSource.Equiv

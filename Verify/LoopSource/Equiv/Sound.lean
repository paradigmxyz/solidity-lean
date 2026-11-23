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
    (h : step x = step y) : Leads step x y := fun k r hk => by
  refine ⟨k, ?_⟩
  cases k with
  | zero => simp [iterate] at hk
  | succ k => simp only [iterate, h] at hk ⊢; exact hk

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
  | .done T, ⟨k, r, hk, hr⟩ => by
    obtain ⟨k', hk'⟩ := hxy k r hk
    exact ⟨k', r, hk', hr⟩
  | .back pred senv st D MO, ⟨env, s, hl, rest⟩ => ⟨env, s, hxy.trans hl, rest⟩
  | .ite e t f, h => by
    simp only [CSound] at h ⊢
    split
    · rename_i h0; rw [if_pos h0] at h; exact CSound.pre hxy f h
    · rename_i h0; rw [if_neg h0] at h; exact CSound.pre hxy t h

theorem atHead_some {fn head : Nat} {pos : Pos} {pred : Nat} (h : atHead fn head pos = some pred) :
    pos = .enter fn pred head := by
  cases pos with
  | enter fn' p b =>
    simp only [atHead] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h
      rw [h]
    · simp at h
  | resume _ _ _ _ => simp [atHead] at h

theorem stackRel_nil {ρ : Val} {call : Call} {ms : List Return} (h : StackRel ρ call ms []) : ms = [] := by
  cases ms with
  | nil => rfl
  | cons _ _ => simp [StackRel] at h

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
    simp only [hat] at h
    cases hsf : stepFoot m pos with
    | none => simp [hsf] at h
    | some dm =>
    obtain ⟨d, mo⟩ := dm
    simp only [hsf] at h
    cases hx : symStep ev cv m sel n K [] pos senv st with
    | none => simp [hx] at h
    | some x =>
    have hn := symStep_sound hc henv m hK hx (ms := []) trivial he hs
    have hfr := frame_step hF hsf hx
    simp only [hx] at h
    cases x with
    | done T =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨r, hr, hobs⟩ := hn
      exact ⟨1, r, iterate_inl hr, hobs⟩
    | go stack pos' senv' st' =>
      cases stack with
      | cons _ _ => simp at h
      | nil =>
      simp only at h
      obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
      obtain rfl := stackRel_nil hst'
      exact CSound.pre (Leads.step hr) t
        (cutRun_sound hc o henv m fn head fuel pos' senv' st' K _ _ t h env' s' he' hs' hK (hfr rfl))
    | fork e stack fn' b yes no senv' st' =>
      cases stack with
      | cons _ _ => simp at h
      | nil =>
      simp only at h
      obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
      obtain rfl := stackRel_nil hst'
      cases hdec : K.lookup e with
      | some bb =>
        have hv := Facts.lookup_sound hK hdec
        cases bb with
        | false =>
          simp only [hdec] at h
          rw [if_pos (hv.mpr rfl)] at hr
          exact CSound.pre (Leads.step hr) t
            (cutRun_sound hc o henv m fn head fuel _ senv' st' K _ _ t h env' s' he' hs' hK (hfr rfl))
        | true =>
          simp only [hdec] at h
          rw [if_neg (fun h0 => by simpa using hv.mp h0)] at hr
          exact CSound.pre (Leads.step hr) t
            (cutRun_sound hc o henv m fn head fuel _ senv' st' K _ _ t h env' s' he' hs' hK (hfr rfl))
      | none =>
      simp only [hdec] at h
      cases ht : cutRun ev cv m sel n fn head fuel (.enter fn' b yes) senv' st' (K.add e true) (D ++ d) (MO ++ mo) with
      | none => simp [ht] at h
      | some tt =>
      cases hf : cutRun ev cv m sel n fn head fuel (.enter fn' b no) senv' st' (K.add e false) (D ++ d) (MO ++ mo) with
      | none => simp [ht, hf] at h
      | some ff =>
      simp only [ht, hf, Option.some.injEq] at h
      subst h
      simp only [CSound]
      by_cases h0 : e.eval ρ = 0
      · rw [if_pos h0]
        rw [if_pos h0] at hr
        exact CSound.pre (Leads.step hr) ff
          (cutRun_sound hc o henv m fn head fuel _ senv' st' _ _ _ ff hf env' s' he' hs'
            (hK.add e false (by simp [h0])) (hfr rfl))
      · rw [if_neg h0]
        rw [if_neg h0] at hr
        exact CSound.pre (Leads.step hr) tt
          (cutRun_sound hc o henv m fn head fuel _ senv' st' _ _ _ tt ht env' s' he' hs'
            (hK.add e true (by simp [h0])) (hfr rfl))

end Verify.LoopSource.Equiv

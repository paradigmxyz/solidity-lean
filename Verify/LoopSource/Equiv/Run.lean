import Verify.LoopSource.Equiv.Match

/-!
# A checked cut-point certificate runs the loop to the tree's result

`loop_mir_runs`: on a call whose words `ρ` the call gives the symbolic run (`CallFactsAt`), a
module whose cut-point certificate checks (`Cut.check`) and whose leaves meet their obligations
(`Obl`) runs, under every oracle the flags allow, to the observable of the tree `T` at `ρ`. The
proof follows the loop: the entry run reaches an end or the header with the template holding at a
header valuation where the invariant holds; from there the iteration run reaches an end or the
header again, at a header valuation where the source loop took one `LoopRecord.Step`, so its
measure fell. Induction on the measure ends it.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement.Generic
open Verify.LoopSource.Interface

/-! ## Valuations of the header -/

theorem trunc_nextVal {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) (hs : List WExpr) :
    trunc n (nextVal n σ hs) = trunc n σ := by
  simp only [trunc, nextVal]
  congr 1
  rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_self]

theorem trunc_self {σ : Val} {n : Nat} (h : σ.args.length = n) : trunc n σ = σ := by
  simp only [trunc]
  rw [List.take_of_length_le (by omega)]

theorem nextVal_ok {n : Nat} {σ : Val} (h : σ.Ok) (hs : List WExpr) : (nextVal n σ hs).Ok := h

/-- What the call gives the run holds at every header valuation of the call. -/
theorem callFactsAt_next {cv : SV} {sel n : Nat} {σ : Val} {call : Call} (hc : CallFactsAt cv sel n σ call)
    (hl : n ≤ σ.args.length) (hcv : ∀ τ : Val, SV.Rel σ call (BitVec.ofNat 256 call.callvalue) cv →
      SV.Rel τ call (BitVec.ofNat 256 call.callvalue) cv) (hs : List WExpr) :
    CallFactsAt cv sel n (nextVal n σ hs) call where
  value := hcv _ hc.value
  size := hc.size
  args i hi hw := by
    rw [hc.args i hi hw]
    simp only [WExpr.eval, nextVal]
    rw [take_getD hi hl]
  selector := hc.selector
  store := hc.store
  ok := hc.ok

theorem envAsk_next {ev : EnvFlags} {o : Oracle} {σ : Val} (h : EnvAsk ev o σ) (n : Nat) (hs : List WExpr) :
    EnvAsk ev o (nextVal n σ hs) :=
  ⟨fun hc => by
    rw [h.caller hc]
    unfold EnvFlags.callerExpr
    split <;> rfl, h.hash⟩

/-! ## The leaves of a run -/

/-- What a leaf of a run says of the frame `x` the run started from, at valuation `σ`: an end
`x` reaches with the leaf tree's observable, or a frame at the header after its phis, which `x`
leads to, holding the template at the next header valuation. -/
def LeafOk (C : Cut) (n : Nat) (blk : Block) (σ : Val) (call : Call) (o : Oracle) (m : Module)
    (x : SolarTV.MIR.Lowered.Frame) : Out → Prop
  | .exit T => ∃ k r, iterate (moduleBlock o call m) k x = some r ∧ observe call r.2 r.1 = (T.eval σ).obs
  | .back hs => ∃ env s, Leads (moduleBlock o call m) x ([], .resume C.fn C.head blk.insts blk.term, env, s) ∧
      EnvRel (nextVal n σ hs) call env (C.env n) ∧ StRel (nextVal n σ hs) s (C.st n)

theorem hold_cons {σ : Val} {K : Facts} {e : WExpr} {b : Bool} (h : K.Hold σ)
    (he : e.eval σ = 0 ↔ b = false) : Facts.Hold σ ((e, b) :: K) := fun p hp => by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact he
  · exact h p hp

theorem header_block {C : Cut} {m : Module} {blk : Block} (h : C.header m = some blk) :
    ∃ f, m.functions[C.fn]? = some f ∧ f.blocks[C.head]? = some blk := by
  unfold Cut.header at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · simp at h

/-- **Some leaf of a run describes the frame**: the one on the sides of the branches `σ` takes. -/
theorem leaves_sound {C : Cut} {n : Nat} {m : Module} {blk : Block} (hblk : C.header m = some blk)
    {σ : Val} (hl : n ≤ σ.args.length) {call : Call} {o : Oracle} {x : SolarTV.MIR.Lowered.Frame} :
    ∀ (t : CTree) (path : Facts) (ls : List (Facts × Out)), t.leaves C n blk path = some ls →
      path.Hold σ → CSound σ call o m C.fn C.head x t →
      ∃ p ∈ ls, p.1.Hold σ ∧ LeafOk C n blk σ call o m x p.2
  | .done T, path, ls, h, hp, hs => by
    simp only [CTree.leaves, Option.some.injEq] at h
    subst h
    exact ⟨_, List.mem_singleton_self _, hp, hs⟩
  | .back pred senv st D MO, path, ls, h, hp, hs => by
    simp only [CTree.leaves] at h
    cases hph : symPhis senv pred blk.phis senv with
    | none => simp [hph] at h
    | some senv1 =>
    simp only [hph] at h
    cases hml : C.matchLeaf n senv1 st (D ++ blk.phis.map Prod.fst) MO with
    | none => simp [hml] at h
    | some hs' =>
    simp only [hml, Option.some.injEq] at h
    subst h
    obtain ⟨env, s, hlead, he, hst, hF⟩ := hs
    obtain ⟨env1, hb, he1⟩ := symPhis_sound he pred blk.phis senv senv1 env hph he
    have hF1 : Frame (D ++ blk.phis.map Prod.fst) MO senv1 st := by
      refine ⟨fun j hj => ?_, hF.2⟩
      simp only [List.mem_append, not_or] at hj
      rw [symPhis_foot _ _ _ hph j hj.2]; exact hF.1 j hj.1
    obtain ⟨hE, hS⟩ := match_rel hl hml hF1 he1 hst
    obtain ⟨f, hf, hbk⟩ := header_block hblk
    refine ⟨_, List.mem_singleton_self _, hp, env1, s, hlead.trans (Leads.same ?_), hE, hS⟩
    simp only [moduleBlock, hf, hbk, hb]
  | .ite e t f, path, ls, h, hp, hs => by
    simp only [CTree.leaves] at h
    cases ht : CTree.leaves C n blk ((e, true) :: path) t with
    | none => simp [ht] at h
    | some a =>
    cases hf : CTree.leaves C n blk ((e, false) :: path) f with
    | none => simp [ht, hf] at h
    | some b =>
    simp only [ht, hf, Option.some.injEq] at h
    subst h
    simp only [CSound] at hs
    by_cases h0 : e.eval σ = 0
    · rw [if_pos h0] at hs
      obtain ⟨p, hpm, hph, hok⟩ := leaves_sound hblk hl f _ _ hf (hold_cons hp (by simp [h0])) hs
      exact ⟨p, List.mem_append_right _ hpm, hph, hok⟩
    · rw [if_neg h0] at hs
      obtain ⟨p, hpm, hph, hok⟩ := leaves_sound hblk hl t _ _ ht (hold_cons hp (by simp [h0])) hs
      exact ⟨p, List.mem_append_left _ hpm, hph, hok⟩

/-! ## The template's footprint -/

theorem lookup_none_of {ids : List (Nat × Slot)} {j : Nat} (h : j ∉ ids.map Prod.fst) :
    ids.lookup j = none := by
  induction ids with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨j', s'⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup]
    have : (j == j') = false := by simp [h.1]
    rw [this]
    exact ih h.2

theorem template_frame (C : Cut) (n : Nat) : Frame (C.ids.map Prod.fst) (C.mem.map Prod.fst) (C.env n) (C.st n) := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · simp only [Cut.env, lookup_none_of hj]
  · simp only [Cut.st, memOf]
    cases hcf : coverFind i C.mem with
    | none => rfl
    | some p =>
      obtain ⟨hpm, h1⟩ := coverFind_some hcf
      exact absurd ⟨p.1, List.mem_map_of_mem hpm, h1⟩ hi

theorem entry_frame (m : Module) :
    Frame [] (entryMO m) (fun _ => .w (.lit 0)) (symEntryStart m SState.initial) := by
  refine ⟨fun _ _ => rfl, fun i hi => ?_⟩
  unfold symEntryStart
  unfold entryMO at hi
  split
  · rename_i f hf
    simp only [hf] at hi
    rw [symStart_mem i hi]
    rfl
  · rfl

/-! ## The loop -/

/-- A frame that leads to the header with the template at `σ`. -/
def AtHead (C : Cut) (n : Nat) (blk : Block) (σ : Val) (call : Call) (o : Oracle) (m : Module)
    (x : SolarTV.MIR.Lowered.Frame) : Prop :=
  ∃ env s, Leads (moduleBlock o call m) x ([], .resume C.fn C.head blk.insts blk.term, env, s) ∧
    EnvRel σ call env (C.env n) ∧ StRel σ s (C.st n)

/-- Each case's iteration run, with its leaves among the iteration leaves. -/
theorem iterLeaves_mem {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {blk : Block} :
    ∀ {Fs : List Facts} {li : List (Facts × Out)}, iterLeaves C ev m sel n blk Fs = some li →
      ∀ F ∈ Fs, ∃ B l, cutRun ev (.w (.lit 0)) m sel n C.fn C.head C.fuel (.resume C.fn C.head blk.insts blk.term)
        (C.env n) (C.st n) F (C.ids.map Prod.fst) (C.mem.map Prod.fst) = some B ∧
        B.leaves C n blk F = some l ∧ ∀ p ∈ l, p ∈ li
  | [], _, _, F, hF => absurd hF List.not_mem_nil
  | G :: Fs, li, h, F, hF => by
    simp only [iterLeaves] at h
    cases hB : cutRun ev (.w (.lit 0)) m sel n C.fn C.head C.fuel (.resume C.fn C.head blk.insts blk.term)
        (C.env n) (C.st n) G (C.ids.map Prod.fst) (C.mem.map Prod.fst) with
    | none => simp [hB] at h
    | some B =>
    cases hr : iterLeaves C ev m sel n blk Fs with
    | none => simp [hB, hr] at h
    | some rest =>
    simp only [hB, hr] at h
    cases hl : B.leaves C n blk G with
    | none => simp [hl] at h
    | some l =>
    simp only [hl, Option.map_some, Option.some.injEq] at h
    subst h
    rcases List.mem_cons.mp hF with rfl | hF
    · exact ⟨B, l, hB, hl, fun p hp => List.mem_append_left _ hp⟩
    · obtain ⟨B', l', h1, h2, h3⟩ := iterLeaves_mem hr F hF
      exact ⟨B', l', h1, h2, fun p hp => List.mem_append_right _ (h3 p hp)⟩

/-- The parts of a check that accepts. -/
theorem check_parts {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel n = some (le, li)) :
    ∃ blk E, C.header m = some blk ∧
      cutRun ev (.w (.lit 0)) m sel n C.fn C.head C.fuel (.enter m.entry 0 0) (fun _ => .w (.lit 0))
        (symEntryStart m SState.initial) [] [] (entryMO m) = some E ∧
      E.leaves C n blk [] = some le ∧ iterLeaves C ev m sel n blk C.cases = some li := by
  unfold Cut.check at hchk
  cases hblk : C.header m with
  | none => simp [hblk] at hchk
  | some blk =>
  simp only [hblk] at hchk
  cases hE : cutRun ev (.w (.lit 0)) m sel n C.fn C.head C.fuel (.enter m.entry 0 0) (fun _ => .w (.lit 0))
      (symEntryStart m SState.initial) [] [] (entryMO m) with
  | none => simp [hE] at hchk
  | some E =>
  cases hI : iterLeaves C ev m sel n blk C.cases with
  | none => simp [hE, hI] at hchk
  | some li' =>
  simp only [hE, hI] at hchk
  cases hle : E.leaves C n blk [] with
  | none => simp [hle] at hchk
  | some le' =>
  simp only [hle, Option.some.injEq, Prod.mk.injEq] at hchk
  obtain ⟨rfl, rfl⟩ := hchk
  exact ⟨blk, E, by first | rfl | assumption, by first | rfl | assumption, by first | rfl | assumption,
    by first | rfl | assumption⟩

/-- **The iterations**: from a header valuation where the invariant holds, the frame reaches the
tree's result, by induction on the source loop's measure. -/
theorem iter_runs {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {le li : List (Facts × Out)}
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    {T : Tree} (hobl : Obl L toSrc X A n C.cases T le li) {call : Call} {o : Oracle} {blk : Block}
    (hblk : C.header m = some blk) (hI : iterLeaves C ev m sel n blk C.cases = some li) :
    ∀ (M : Nat) (σ : Val) (x : SolarTV.MIR.Lowered.Frame), (L (trunc n σ)).m (toSrc σ) < M →
      n ≤ σ.args.length →
      CallFactsAt (.w (.lit 0)) sel n σ call → EnvAsk ev o σ → A (trunc n σ) → (L (trunc n σ)).P (toSrc σ) →
      X σ → AtHead C n blk σ call o m x →
      ∃ k r, iterate (moduleBlock o call m) k x = some r ∧ observe call r.2 r.1 = (T.eval (trunc n σ)).obs
  | 0, _, _, hM, _, _, _, _, _, _, _ => absurd hM (Nat.not_lt_zero _)
  | M + 1, σ, x, hM, hl, hc, henv, hA, hP, hX, ⟨env, s, hlead, he, hs⟩ => by
    have hok : σ.Ok := hc.ok
    obtain ⟨F, hFm, hFh⟩ := hobl.facts σ hl hok hA hP hX
    obtain ⟨B, l, hB, hli, hsub⟩ := iterLeaves_mem hI F hFm
    have hsB := cutRun_sound hc o henv m C.fn C.head C.fuel _ _ _ _ _ _ B hB env s he hs hFh
      (template_frame C n)
    obtain ⟨p, hpm, hph, hleaf⟩ := leaves_sound hblk hl B F _ hli hFh hsB
    have hob := hobl.iter σ hl hok hA hP hX p (hsub p hpm) hph
    cases hp2 : p.2 with
    | exit T' =>
      rw [hp2] at hleaf hob
      obtain ⟨k, r, hk, hr⟩ := hleaf
      obtain ⟨k', hk'⟩ := hlead k r hk
      exact ⟨k', r, hk', hr.trans hob⟩
    | back hs' =>
      rw [hp2] at hleaf hob
      obtain ⟨hstep, hX'⟩ := hob
      obtain ⟨env', s', hlead', he', hst'⟩ := hleaf
      have ih := iter_runs hobl hblk hI M (nextVal n σ hs') x
        (by rw [trunc_nextVal hl]; have := hstep.2.2.2; omega) (by rw [nextVal_len hl]; omega)
        (callFactsAt_next hc hl (fun _ h => by simpa [SV.Rel, WExpr.eval] using h) hs')
        (envAsk_next henv n hs')
        (by rw [trunc_nextVal hl]; exact hA) (by rw [trunc_nextVal hl]; exact hstep.2.2.1) hX'
        ⟨env', s', hlead.trans hlead', he', hst'⟩
      rw [trunc_nextVal hl] at ih
      exact ih

/-- **A checked loop runs to the tree's result**: from the module's entry, on a call of `n` words
`ρ` that `A` admits, under every oracle the flags allow. -/
theorem loop_mir_runs {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel n = some (le, li)) {L : Val → LoopRecord} {toSrc : Val → Val}
    {X A : Val → Prop} {T : Tree} (hobl : Obl L toSrc X A n C.cases T le li) {ρ : Val} {call : Call}
    (hc : CallFactsAt (.w (.lit 0)) sel n ρ call) (hlen : ρ.args.length = n) (hA : A ρ) (o : Oracle)
    (henv : EnvAsk ev o ρ) :
    (moduleSem o).run m call = some (T.eval ρ).obs := by
  obtain ⟨blk, E, hblk, hE, hle, hI⟩ := check_parts hchk
  have hz : EnvRel ρ call (fun _ => 0) (fun _ => .w (.lit 0)) := fun _ => by
    simp [SV.Rel, WExpr.eval]
  have hsE := cutRun_sound hc o henv m C.fn C.head C.fuel _ _ _ _ _ _ E hE _ _ hz
    ((StRel.initial call hc.store hc.ok).entryStart m) (fun _ h => absurd h List.not_mem_nil) (entry_frame m)
  have hl : n ≤ ρ.args.length := by omega
  obtain ⟨p, hpm, hph, hleaf⟩ := leaves_sound hblk hl E [] _ hle (fun _ h => absurd h List.not_mem_nil) hsE
  have hob := hobl.entry ρ hlen hc.ok hA p hpm hph
  have ends : ∃ k r, Module.run o m call k = some r ∧ observe call r.2 r.1 = (T.eval ρ).obs := by
    cases hp2 : p.2 with
    | exit T' =>
      rw [hp2] at hleaf hob
      obtain ⟨k, r, hk, hr⟩ := hleaf
      exact ⟨k, r, hk, hr.trans hob⟩
    | back hs =>
      rw [hp2] at hleaf hob
      obtain ⟨hP, hX⟩ := hob
      obtain ⟨env', s', hlead, he', hst'⟩ := hleaf
      have htr : trunc n (nextVal n ρ hs) = ρ := by rw [trunc_nextVal hl, trunc_self hlen]
      have h := iter_runs hobl hblk hI ((L ρ).m (toSrc (nextVal n ρ hs)) + 1) (nextVal n ρ hs) _
        (by rw [htr]; exact Nat.lt_succ_self _) (by rw [nextVal_len hl]; omega)
        (callFactsAt_next hc hl (fun _ h => by simpa [SV.Rel, WExpr.eval] using h) hs)
        (envAsk_next henv n hs) (by rw [htr]; exact hA) (by rw [htr]; exact hP) hX
        ⟨env', s', hlead, he', hst'⟩
      rw [htr] at h
      exact h
  obtain ⟨k, r, hk, hr⟩ := ends
  have e : moduleLayer.result o m call = some r := moduleLayer.result_of_ends ⟨k, hk⟩
  show (moduleLayer.result o m call).map _ = _
  rw [e, ← hr]
  rfl

end Verify.LoopSource.Equiv

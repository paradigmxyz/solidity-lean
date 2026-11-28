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

/-- What the call gives the run holds at every header valuation over the call. -/
theorem callFactsAt_trunc {sel n : Nat} {σ : Val} {call : Call} (hl : n ≤ σ.args.length)
    (hc : CallFactsAt (.w (.lit 0)) sel n (trunc n σ) call) : CallFactsAt (.w (.lit 0)) sel n σ call :=
  { hc with
    value := hc.value
    args := fun i hi hw => by
      rw [hc.args i hi hw]
      simp only [WExpr.eval, trunc]
      rw [← take_getD hi hl [], List.append_nil] }

theorem envAsk_trunc {ev : EnvFlags} {o : Oracle} {n : Nat} {σ : Val} (h : EnvAsk ev o (trunc n σ)) :
    EnvAsk ev o σ :=
  ⟨fun hc => by
    rw [h.caller hc]
    unfold EnvFlags.callerExpr
    split <;> rfl, h.hash⟩

/-! ## The leaves of a run -/

/-- A frame that leads to the header with the template at `σ`. -/
def AtHead (C : Cut) (n : Nat) (blk : Block) (σ : Val) (call : Call) (o : Oracle) (m : Module)
    (x : SolarTV.MIR.Lowered.Frame) : Prop :=
  ∃ env s, Leads (moduleBlock o call m) x ([], .resume C.fn C.head blk.insts blk.term, env, s) ∧
    EnvRel σ call env (C.env n) ∧ StRel σ s (C.st n)

/-- What a leaf of a run says of the frame `x` the run started from, at valuation `σ`: an end
`x` reaches with the leaf tree's observable, or a frame at the header after its phis, which `x`
leads to, holding the template at the next header valuation. -/
def LeafOk (C : Cut) (n : Nat) (blk : Block) (σ : Val) (call : Call) (o : Oracle) (m : Module)
    (x : SolarTV.MIR.Lowered.Frame) : Out → Prop
  | .exit T => ∃ k r, iterate (moduleBlock o call m) k x = some r ∧ observe call r.2 r.1 = (T.eval σ).obs
  | .back hs => AtHead C n blk (nextVal n σ hs) call o m x

/-- **Some leaf of a run describes the frame**: the one on the sides of the branches `σ` takes. -/
theorem leaves_sound {C : Cut} {n : Nat} {m : Module} {blk : Block} (hblk : C.header m = some blk)
    {σ : Val} (hl : n ≤ σ.args.length) {call : Call} {o : Oracle} {x : SolarTV.MIR.Lowered.Frame} :
    ∀ (t : CTree) (path : Facts) (ls : List (Facts × Out)), t.leaves C n blk path = some ls →
      path.Hold σ → CSound σ call o m C.fn C.head x t →
      ∃ p ∈ ls, p.1.Hold σ ∧ LeafOk C n blk σ call o m x p.2
  | .done T, path, ls, h, hp, hs => by
    cases h
    exact ⟨_, List.mem_singleton_self _, hp, hs⟩
  | .back pred senv st D MO, path, ls, h, hp, ⟨env, s, hlead, he, hst, hF⟩ => by
    simp only [CTree.leaves] at h
    split at h <;> try contradiction
    rename_i senv1 hph
    split at h <;> try contradiction
    rename_i hs' hml
    cases h
    obtain ⟨env1, hb, he1⟩ := symPhis_sound he pred blk.phis senv senv1 env hph he
    have hF1 : Frame (D ++ blk.phis.map Prod.fst) MO senv1 st := by
      refine ⟨fun j hj => ?_, hF.2⟩
      simp only [List.mem_append, not_or] at hj
      rw [symPhis_foot _ _ _ hph j hj.2]; exact hF.1 j hj.1
    obtain ⟨hE, hS⟩ := match_rel hl hml hF1 he1 hst
    unfold Cut.header at hblk
    split at hblk <;> try contradiction
    refine ⟨_, List.mem_singleton_self _, hp, env1, s, hlead.trans (Leads.same ?_), hE, hS⟩
    simp only [moduleBlock, *]
  | .ite e t f, path, ls, h, hp, hs => by
    simp only [CTree.leaves] at h
    split at h <;> try contradiction
    rename_i a b ht hf
    cases h
    simp only [CSound] at hs
    have hold (b : Bool) (hb : e.eval σ = 0 ↔ b = false) : Facts.Hold σ ((e, b) :: path) := fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb
      · exact hp q hq
    split at hs
    · obtain ⟨p, hpm, hph, hok⟩ := leaves_sound hblk hl f _ _ hf (hold false (by simp [*])) hs
      exact ⟨p, List.mem_append_right _ hpm, hph, hok⟩
    · obtain ⟨p, hpm, hph, hok⟩ := leaves_sound hblk hl t _ _ ht (hold true (by simp [*])) hs
      exact ⟨p, List.mem_append_left _ hpm, hph, hok⟩

/-! ## The template's footprint -/

theorem template_frame (C : Cut) (n : Nat) : Frame (C.ids.map Prod.fst) (C.mem.map Prod.fst) (C.env n) (C.st n) := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have : C.ids.lookup j = none := by
      cases h : C.ids.lookup j with
      | none => rfl
      | some s => exact absurd (List.mem_map_of_mem (f := Prod.fst) (lookup_mem h)) hj
    simp only [Cut.env, this]
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

/-- Each case's iteration run, with its leaves among the iteration leaves. -/
theorem iterLeaves_mem {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {blk : Block} :
    ∀ {Fs : List Facts} {li : List (Facts × Out)}, iterLeaves C ev m sel n blk Fs = some li →
      ∀ F ∈ Fs, ∃ B l, cutRun ev (.w (.lit 0)) m sel n C.fn C.head C.fuel (.resume C.fn C.head blk.insts blk.term)
        (C.env n) (C.st n) F (C.ids.map Prod.fst) (C.mem.map Prod.fst) = some B ∧
        B.leaves C n blk F = some l ∧ ∀ p ∈ l, p ∈ li
  | [], _, _, F, hF => absurd hF List.not_mem_nil
  | G :: Fs, li, h, F, hF => by
    simp only [iterLeaves] at h
    split at h <;> try contradiction
    rename_i B rest hB hr
    cases hl : B.leaves C n blk G <;> simp only [hl, Option.map_none, Option.map_some, Option.some.injEq] at h
    · contradiction
    subst h
    rcases List.mem_cons.mp hF with rfl | hF
    · exact ⟨B, _, hB, hl, fun p hp => List.mem_append_left _ hp⟩
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
  split at hchk <;> try contradiction
  split at hchk <;> try contradiction
  split at hchk <;> try contradiction
  cases hchk
  exact ⟨_, _, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- **The iterations**: from a header valuation over the call `ρ` where the invariant holds, the
frame reaches the tree's result, by induction on the source loop's measure. -/
theorem iter_runs {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {le li : List (Facts × Out)}
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    {T : Tree} (hobl : Obl L toSrc X A n C.cases T le li) {call : Call} {o : Oracle} {blk : Block}
    (hblk : C.header m = some blk) (hI : iterLeaves C ev m sel n blk C.cases = some li) {ρ : Val}
    (hc : CallFactsAt (.w (.lit 0)) sel n ρ call) (henv : EnvAsk ev o ρ) (hA : A ρ)
    (σ : Val) (x : SolarTV.MIR.Lowered.Frame) (hρ : trunc n σ = ρ) (hl : n ≤ σ.args.length)
    (hP : (L ρ).P (toSrc σ)) (hX : X σ) (hx : AtHead C n blk σ call o m x) :
    ∃ k r, iterate (moduleBlock o call m) k x = some r ∧ observe call r.2 r.1 = (T.eval ρ).obs := by
  subst hρ
  obtain ⟨env, s, hlead, he, hs⟩ := hx
  have hc' := callFactsAt_trunc hl hc
  obtain ⟨F, hFm, hFh⟩ := hobl.facts σ hl hc'.ok hA hP hX
  obtain ⟨B, l, hB, hli, hsub⟩ := iterLeaves_mem hI F hFm
  obtain ⟨p, hpm, hph, hleaf⟩ := leaves_sound hblk hl B F _ hli hFh
    (cutRun_sound hc' o (envAsk_trunc henv) m C.fn C.head C.fuel _ _ _ _ _ _ B hB env s he hs hFh
      (template_frame C n))
  have hob := hobl.iter σ hl hc'.ok hA hP hX p (hsub p hpm) hph
  revert hleaf hob
  cases p.2 with
  | exit T' => exact fun ⟨k, r, hk, hr⟩ hob => (hlead k r hk).imp fun _ hk' => ⟨r, hk', hr.trans hob⟩
  | back hs' =>
    intro ⟨env', s', hlead', he', hst'⟩ ⟨hstep, hX'⟩
    exact iter_runs hobl hblk hI hc henv hA _ x (trunc_nextVal hl hs') (by rw [nextVal_len hl]; omega)
      hstep.2.2.1 hX' ⟨env', s', hlead.trans hlead', he', hst'⟩
termination_by (L (trunc n σ)).m (toSrc σ)
decreasing_by rw [trunc_nextVal hl]; exact hstep.2.2.2

/-- **A checked loop runs to the tree's result**: from the module's entry, on a call of `n` words
`ρ` that `A` admits, under every oracle the flags allow. -/
theorem loop_mir_runs {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel n = some (le, li)) {L : Val → LoopRecord} {toSrc : Val → Val}
    {X A : Val → Prop} {T : Tree} (hobl : Obl L toSrc X A n C.cases T le li) {ρ : Val} {call : Call}
    (hc : CallFactsAt (.w (.lit 0)) sel n ρ call) (hlen : ρ.args.length = n) (hA : A ρ) (o : Oracle)
    (henv : EnvAsk ev o ρ) :
    (moduleSem o).run m call = some (T.eval ρ).obs := by
  obtain ⟨blk, E, hblk, hE, hle, hI⟩ := check_parts hchk
  have hl : n ≤ ρ.args.length := hlen.ge
  obtain ⟨p, hpm, hph, hleaf⟩ := leaves_sound hblk hl E [] _ hle (fun _ h => absurd h List.not_mem_nil)
    (cutRun_sound hc o henv m C.fn C.head C.fuel _ _ _ _ _ _ E hE (fun _ => 0) _
      (fun _ => by simp [SV.Rel, WExpr.eval]) ((StRel.initial call hc.store hc.ok).entryStart m)
      (fun _ h => absurd h List.not_mem_nil) (entry_frame m))
  have hob := hobl.entry ρ hlen hc.ok hA p hpm hph
  obtain ⟨k, r, hk, hr⟩ : ∃ k r, Module.run o m call k = some r ∧ observe call r.2 r.1 = (T.eval ρ).obs := by
    revert hleaf hob
    cases p.2 with
    | exit T' => exact fun ⟨k, r, hk, hr⟩ hob => ⟨k, r, hk, hr.trans hob⟩
    | back hs =>
      exact fun hx ⟨hP, hX⟩ => iter_runs hobl hblk hI hc henv hA _ _
        (by rw [trunc_nextVal hl, trunc_self hlen]) (by rw [nextVal_len hl]; omega) hP hX hx
  show (moduleLayer.result o m call).map _ = _
  rw [moduleLayer.result_of_ends ⟨k, hk⟩, ← hr]
  rfl

end Verify.LoopSource.Equiv

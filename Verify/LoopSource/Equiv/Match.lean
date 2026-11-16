import Verify.LoopSource.Equiv.Sound

/-!
# An arrival that matches the template holds the template at the next header valuation

\`match_rel\`: when \`Cut.matchLeaf\` accepts an arrival (values \`senv1\` after the header's phis,
state \`st\`), every machine frame that holds the arrival on a valuation \`σ\` holds the template on
\`nextVal n σ hs\`, the valuation whose header words are the ones the match read.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement.Generic

/-! ## Valuations -/

theorem take_getD {l : List Nat} {n i : Nat} (hi : i < n) (hl : n ≤ l.length) (rest : List Nat) :
    (l.take n ++ rest).getD i 0 = l.getD i 0 := by
  have h1 : i < (l.take n).length := by simp; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, List.getElem?_take_of_lt hi]

/-- A word over the call's words has the same value at the next header valuation. -/
theorem eval_below {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) (hs : List WExpr) :
    ∀ e : WExpr, argsBelow n e = true → e.eval (nextVal n σ hs) = e.eval σ
  | .lit _, _ => rfl
  | .arg i, h => by
    simp only [argsBelow, decide_eq_true_eq] at h
    simp only [WExpr.eval, nextVal]
    rw [take_getD h hl]
  | .init _, _ => rfl
  | .un _ a, h => by simp only [WExpr.eval]; rw [eval_below hl hs a h]
  | .bin _ a b, h => by
    simp only [argsBelow, Bool.and_eq_true] at h
    simp only [WExpr.eval]; rw [eval_below hl hs a h.1, eval_below hl hs b h.2]
  | .sinit k, h => by simp only [WExpr.eval]; rw [eval_below hl hs k h]; rfl
  | .sel c a b, h => by
    simp only [argsBelow, Bool.and_eq_true] at h
    simp only [WExpr.eval]; rw [eval_below hl hs c h.1.1, eval_below hl hs a h.1.2, eval_below hl hs b h.2]
  | .hash a b, h => by
    simp only [argsBelow, Bool.and_eq_true] at h
    simp only [WExpr.eval]; rw [eval_below hl hs a h.1, eval_below hl hs b h.2]; rfl
  | .caller, _ => rfl

theorem nextVal_len {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) (hs : List WExpr) :
    (nextVal n σ hs).args.length = n + hs.length := by
  simp [nextVal]; omega

/-- Header word \`k\` at the next header valuation is the value of the \`k\`-th word read. -/
theorem eval_hw {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) {hs : List WExpr} {k : Nat} {e : WExpr}
    (h : hs[k]? = some e) : (WExpr.arg (n + k)).eval (nextVal n σ hs) = e.eval σ := by
  have hk : k < hs.length := by
    rcases Nat.lt_or_ge k hs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have ht : (σ.args.take n).length = n := by simp; omega
  simp only [WExpr.eval, nextVal]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ht, Nat.add_sub_cancel_left,
    List.getElem?_map, h]
  simp only [Option.map_some, Option.getD_some]
  exact Nat.mod_eq_of_lt (WExpr.eval_lt σ e)

/-- A slot that holds a word gives it its value at the next header valuation. -/
theorem slot_eval {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) {hs : List WExpr} {s : Slot}
    {e : WExpr} (hok : slotOk n hs s e = true) : (s.expr n).eval (nextVal n σ hs) = e.eval σ := by
  cases s with
  | hw k =>
    simp only [slotOk, decide_eq_true_eq] at hok
    exact eval_hw hl hok
  | fixed f =>
    simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, hb⟩ := hok
    exact eval_below hl hs _ hb

/-! ## The pairs -/

theorem idPairs_mem {senv : SEnv} : ∀ {ids : List (Nat × Slot)} {ps : List (Slot × WExpr)},
    idPairs senv ids = some ps → ∀ p ∈ ids, ∃ e, senv p.1 = .w e ∧ (p.2, e) ∈ ps
  | [], _, _, p, hp => absurd hp List.not_mem_nil
  | (j, s) :: rest, ps, h, p, hp => by
    simp only [idPairs] at h
    split at h
    · rename_i e ps' hj hr
      simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨e, hj, List.mem_cons_self ..⟩
      · obtain ⟨e', h1, h2⟩ := idPairs_mem hr p hp
        exact ⟨e', h1, List.mem_cons_of_mem _ h2⟩
    · simp at h

theorem memPairs_mem {mem : Nat → OByte} : ∀ {ms : List (Nat × Slot)} {ps : List (Slot × WExpr)},
    memPairs mem ms = some ps → ∀ p ∈ ms, ∃ e, memWord mem p.1 = some e ∧ (p.2, e) ∈ ps
  | [], _, _, p, hp => absurd hp List.not_mem_nil
  | (o, s) :: rest, ps, h, p, hp => by
    simp only [memPairs] at h
    split at h
    · rename_i e ps' hj hr
      simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨e, hj, List.mem_cons_self ..⟩
      · obtain ⟨e', h1, h2⟩ := memPairs_mem hr p hp
        exact ⟨e', h1, List.mem_cons_of_mem _ h2⟩
    · simp at h

theorem memWord_byte {mem : Nat → OByte} {o : Nat} {e : WExpr} (h : memWord mem o = some e)
    {j : Nat} (hj : j < 32) : mem (o + j) = .byteOf e j := by
  unfold memWord at h
  split at h
  · split at h
    · rename_i hall
      simp only [Option.some.injEq] at h
      subst h
      have := List.all_eq_true.mp hall j (List.mem_range.mpr hj)
      simpa using this
    · simp at h
  · simp at h

theorem coverFind_some {i : Nat} : ∀ {ms : List (Nat × Slot)} {p : Nat × Slot},
    coverFind i ms = some p → p ∈ ms ∧ p.1 ≤ i ∧ i < p.1 + 32
  | [], _, h => by simp [coverFind] at h
  | (o, s) :: rest, p, h => by
    simp only [coverFind] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self .., hc⟩
    · obtain ⟨h1, h2⟩ := coverFind_some h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem coverFind_none {i : Nat} : ∀ {ms : List (Nat × Slot)}, coverFind i ms = none →
    ∀ p ∈ ms, ¬ (p.1 ≤ i ∧ i < p.1 + 32)
  | [], _, p, hp => absurd hp List.not_mem_nil
  | (o, s) :: rest, h, p, hp => by
    simp only [coverFind] at h
    split at h
    · simp at h
    · rename_i hc
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hc
      · exact coverFind_none h p hp

/-- The storage after two lists of writes with the same keys and the same values agrees. -/
theorem store_pairs {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) {hs : List WExpr} :
    ∀ {ws : Writes} {cs : List (WExpr × Slot)} {ps : List (Slot × WExpr)},
      writePairs ws cs = some ps → cs.all (fun w => argsBelow n w.1) = true →
      (∀ p ∈ ps, (p.1.expr n).eval (nextVal n σ hs) = p.2.eval σ) →
      ∀ k, Writes.store (nextVal n σ hs) (cs.map (fun p => (p.1, p.2.expr n))) k = Writes.store σ ws k
  | [], [], _, _, _, _, k => rfl
  | (k', e) :: ws, (k'', s) :: cs, ps, h, hb, hv, k => by
    simp only [writePairs] at h
    split at h
    · rename_i hk
      subst hk
      cases hr : writePairs ws cs with
      | none => simp [hr] at h
      | some ps' =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [List.all_cons, Bool.and_eq_true] at hb
      simp only [List.map_cons, Writes.store]
      rw [eval_below hl hs _ hb.1, hv (s, e) (List.mem_cons_self ..),
        store_pairs hl hr hb.2 (fun p hp => hv p (List.mem_cons_of_mem _ hp)) k]
    · simp at h
  | [], _ :: _, _, h, _, _, _ => by simp [writePairs] at h
  | _ :: _, [], _, h, _, _, _ => by simp [writePairs] at h


/-! ## The match -/

theorem lookup_mem : ∀ {ids : List (Nat × Slot)} {j : Nat} {s : Slot}, ids.lookup j = some s → (j, s) ∈ ids
  | [], _, _, h => by simp [List.lookup] at h
  | (j', s') :: rest, j, s, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hj
      simp only [Option.some.injEq] at h
      subst h
      have : j = j' := by simpa using hj
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_none : ∀ {ids : List (Nat × Slot)} {j : Nat}, ids.lookup j = none → j ∉ ids.map Prod.fst
  | [], _, _ => by simp
  | (j', s') :: rest, j, h => by
    simp only [List.lookup] at h
    split at h
    · simp at h
    · rename_i hj
      have hne : j ≠ j' := fun e => by simp [e] at hj
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨hne, lookup_none h⟩

/-- **A matched arrival holds the template at the next header valuation.** -/
theorem match_rel {C : Cut} {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) {senv : SEnv}
    {st : SState} {D MO : List Nat} {hs : List WExpr} (hm : C.matchLeaf n senv st D MO = some hs)
    (hF : Frame D MO senv st) {call : Call} {env : Env} {s : State} (he : EnvRel σ call env senv)
    (hs' : StRel σ s st) :
    EnvRel (nextVal n σ hs) call env (C.env n) ∧ StRel (nextVal n σ hs) s (C.st n) := by
  unfold Cut.matchLeaf at hm
  cases hlp : leafPairs C senv st with
  | none => simp [hlp] at hm
  | some ps =>
  simp only [hlp] at hm
  split at hm
  · rename_i hchk
    simp only [Option.some.injEq] at hm
    subst hm
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hchk
    obtain ⟨⟨⟨⟨hslots, hkeys⟩, hD⟩, hMO⟩, hlogs⟩ := hchk
    unfold leafPairs at hlp
    cases ha : idPairs senv C.ids with
    | none => simp [ha] at hlp
    | some pa =>
    cases hb : memPairs st.mem C.mem with
    | none => simp [ha, hb] at hlp
    | some pb =>
    cases hc : writePairs st.writes C.writes with
    | none => simp [ha, hb, hc] at hlp
    | some pc =>
    simp only [ha, hb, hc, Option.some.injEq] at hlp
    subst hlp
    have hval : ∀ p ∈ pa ++ pb ++ pc, (p.1.expr n).eval (nextVal n σ (hwOf C.nhw (pa ++ pb ++ pc))) = p.2.eval σ :=
      fun p hp => slot_eval hl (hslots p hp)
    refine ⟨fun j => ?_, ⟨fun i => ?_, fun k => ?_, ?_⟩⟩
    · -- values
      unfold Cut.env
      cases hlk : C.ids.lookup j with
      | some sl =>
        simp only [SV.Rel]
        obtain ⟨e, hj, hmem⟩ := idPairs_mem ha (j, sl) (lookup_mem hlk)
        have h1 := he j
        rw [hj] at h1
        simp only [SV.Rel] at h1
        rw [h1, hval (sl, e) (by simp [hmem])]
      | none =>
        have hnD : j ∉ D := fun hj => lookup_none hlk (hD j hj)
        have h1 := he j
        rw [hF.1 j hnD] at h1
        exact h1
    · -- memory
      rw [hs'.mem i]
      simp only [Cut.st, memOf]
      cases hcf : coverFind i C.mem with
      | some p =>
        obtain ⟨o, sl⟩ := p
        obtain ⟨hpm, hlo, hhi⟩ := coverFind_some hcf
        obtain ⟨e, hw, hmem⟩ := memPairs_mem hb (o, sl) hpm
        have hbyte := memWord_byte hw (j := i - o) (by simp at hlo hhi; omega)
        have hi : o + (i - o) = i := by simp at hlo; omega
        rw [hi] at hbyte
        simp only [hbyte, OByte.eval]
        rw [hval (sl, e) (by simp [hmem])]
      | none =>
        have hnc : ¬ Covered MO i := by
          rintro ⟨o, ho, h1⟩
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hMO o ho)
          exact coverFind_none hcf p hp h1
        rw [hF.2 i hnc]
        rfl
    · -- storage
      rw [hs'.store k]
      simp only [Cut.st]
      exact (store_pairs hl hc (List.all_eq_true.mpr fun w hw => hkeys w hw)
        (fun p hp => hval p (by simp [hp])) k.toNat).symm
    · -- logs
      rw [hs'.world, hlogs]
      rfl
  · simp at hm

end Verify.LoopSource.Equiv

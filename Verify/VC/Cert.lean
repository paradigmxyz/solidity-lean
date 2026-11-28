import Verify.VC.Discharge

/-!
# Certificate-checked discharge

The search of `refuteOb` (Verify/VC/Discharge.lean) is cheap compiled and expensive in the kernel:
every case split first runs Fourier-Motzkin to exhaustion, and each elimination picks its term by
counting every candidate. Here the search runs compiled (`certOb`, not trusted) and records what it
found as a `Cert`: which case splits it took, and, where a branch closes, the nonnegative
multipliers of the branch's constraints `l ≤ 0` whose sum is a positive constant (a Farkas
combination, read off Fourier-Motzkin's eliminations). The kernel then only replays the tableau
along the certificate and adds up the multiplied constraints (`refuteC`, `farkas`);
`refuteObC_sound` shows that an accepted certificate refutes the obligation, whatever produced
it. A wrong certificate makes the check answer `false`: it fails closed.
-/

namespace SolidCore.Verify.VC

/-- How one branch of the tableau closes: `leaf w` at its next case split (or when its facts run
out) by the constraints multiplied by `w`, `br hs` by taking that split, one certificate per case. -/
inductive Cert where
  | leaf (w : List Nat)
  | br (hs : List Cert)
  /-- At a case split: move its fact to the end of the list, so that the facts after it are read
  first. -/
  | later (c : Cert)
  /-- At the top only: read only the facts the mask keeps (a missing entry keeps the fact). -/
  | keep (m : List Bool) (c : Cert)
  deriving Repr, Inhabited

/-- The certificate under a later step, if it is one. -/
def Cert.later? : Cert → Option Cert
  | .later c => some c
  | _ => none

/-- `Σ w_i * l_i`, skipping zero multipliers. -/
def farkasSum : List Nat → List Lin → Lin
  | w :: ws, l :: ls => if w = 0 then farkasSum ws ls else (l.scale w).add (farkasSum ws ls)
  | _, _ => ⟨0, []⟩

/-- The constraints `l ≤ 0`, multiplied by `w` and added up, give a positive constant. -/
def farkas (w : List Nat) (cs : List Lin) : Bool :=
  let l := (farkasSum w cs).norm
  l.cs.isEmpty && decide (0 < l.k)

/-- A linear form with the equations substituted in its terms, merged again. -/
def Lin.substE (eqs : List (Tm × Tm)) (l : Lin) : Lin :=
  (Lin.mk l.k (l.cs.map fun p => (substN eqs substFuel p.1, p.2))).norm

/-- The facts a mask keeps; a missing entry keeps the fact. -/
def keepMask : List Bool → List Tm → List Tm
  | b :: bs, t :: ts => if b then t :: keepMask bs ts else keepMask bs ts
  | [], ts => ts
  | _ :: _, [] => []

theorem mem_keepMask : ∀ (m : List Bool) (ts : List Tm) {t : Tm}, t ∈ keepMask m ts → t ∈ ts
  | b :: bs, u :: us, t, h => by
    simp only [keepMask] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_keepMask bs us h)
    · exact List.mem_cons_of_mem _ (mem_keepMask bs us h)
  | [], _, _, h => by simpa [keepMask] using h
  | _ :: _, [], _, h => by simp [keepMask] at h

/-- The tableau of `refute`, along a certificate: no search, and Fourier-Motzkin replaced by the
check of a Farkas combination. -/
def refuteC (ks : List String) : Nat → List Tm → List Lin → Cert → Bool
  | 0, _, _, _ => false
  | _ + 1, [], cs, c => match c with
    | .leaf w => farkas w cs
    | _ => false
  | n + 1, t :: rest, cs, c =>
    match step ks t with
    | .drop => refuteC ks n rest cs c
    | .closed => true
    | .facts ts => refuteC ks n (ts ++ rest) cs c
    | .cons ls => refuteC ks n rest (ls ++ cs) c
    | .split bs => match c with
      | .leaf w => farkas w cs
      | .later c' => refuteC ks n (rest ++ [t]) cs c'
      | .keep _ _ => false
      | .br hs => bs.length == hs.length && (bs.zip hs).all fun p => refuteC ks n (p.1 ++ rest) cs p.2
    | .ite c' t1 t2 => match c with
      | .leaf w => farkas w cs
      | .br [h1, h2] =>
        refuteC ks n (c' :: ((t1 :: rest).map (resolve c' true resolveFuel)).map
            (substN (iteEqs c') substFuel)) (cs.map (Lin.substE (iteEqs c'))) h1 &&
          refuteC ks n (neg c' :: (t2 :: rest).map (resolve c' false resolveFuel)) cs h2
      | .later c'' => refuteC ks n (rest ++ [t]) cs c''
      | _ => false
    | .skolem x t =>
      if fresh x rest cs then refuteC ks n (t :: rest) cs c
      else if fresh (x ++ "'") (t :: rest) cs then
        refuteC ks n (t.subst .int x (.ivar (x ++ "'")) :: rest) cs c
      else refuteC ks n rest cs c

/-- `refuteOb` along a certificate; `d` adds the facts of `mod` and `div`. -/
def refuteObC (fs : List Tm) (d : Bool) (c : Cert) : Bool :=
  let eqs := fs.filterMap eqOf?
  let gs := (fs.filter fun t => (eqOf? t).isNone).map fun t => rowN rowFuel (substN eqs substFuel t)
  let rs := relevant gs
  let ts := if d then goalFirst rs ++ divFacts rs else goalFirst rs
  match c with
  | .keep m c' => refuteC (goalBinders rs) stepFuel (keepMask m ts) [] c'
  | c => refuteC (goalBinders rs) stepFuel ts [] c

/-- `dischargeAt` along a certificate. -/
def dischargeAtC (cs : List Cmd) (i : Nat) (d : Bool) (c : Cert) : Bool :=
  let fs := (obligations cs).getD i []
  isProbe fs || refuteObC fs d c

/-! ## Producing certificates (compiled, not trusted) -/

/-- `w * a` plus `v * b`, pointwise. -/
def combW (v : Nat) (a : List Nat) (w : Nat) (b : List Nat) : List Nat :=
  List.zipWith (fun x y => v * x + w * y) a b

/-- `elim`, each constraint carrying its multipliers of the input constraints. -/
def elimW (x : Tm) (cs : List (Lin × List Nat)) : List (Lin × List Nat) :=
  let pos := cs.filter fun l => decide (0 < coeff l.1 x)
  let neg := cs.filter fun l => decide (coeff l.1 x < 0)
  cs.filter (fun l => decide (coeff l.1 x = 0)) ++
    pos.flatMap fun p => neg.map fun q =>
      (((p.1.scale (-(coeff q.1 x))).add (q.1.scale (coeff p.1 x))).norm,
        combW (-(coeff q.1 x)).toNat p.2 (coeff p.1 x).toNat q.2)

/-- `fm`, returning the multipliers of a contradiction. -/
def fmW : Nat → List (Lin × List Nat) → Option (List Nat)
  | 0, _ => none
  | n + 1, cs =>
    let cs := cs.filter fun l => !(l.1.cs.isEmpty && decide (l.1.k ≤ 0))
    match cs.find? (fun l => l.1.cs.isEmpty && decide (0 < l.1.k)) with
    | some l => some l.2
    | none =>
      let ls := cs.map (·.1)
      match pickVar ls with
      | none => none
      | some x => if elimCost ls x ≤ 256 ∧ cs.length ≤ 512 then fmW n (elimW x cs) else none

/-- Fourier-Motzkin on `cs`, as a certificate (multipliers tracked only once `fm` succeeds). -/
def fmCert (F : Nat) (cs : List Lin) : Option Cert :=
  if !fm F cs then none else
  let m := cs.length
  let unit := fun i => (List.range m).map fun j => if i = j then 1 else 0
  (fmW F (cs.zipIdx.map fun (l, i) => (l, unit i))).map .leaf

/-- `refute`, returning the certificate of what it found. -/
def refuteG (F : Nat) (ks : List String) : Nat → Nat → List Tm → List Lin → Option Cert
  | 0, _, _, _ => none
  | _ + 1, _, [], cs => fmCert F cs
  | n + 1, b, t :: rest, cs =>
    match step ks t with
    | .drop => refuteG F ks n b rest cs
    | .closed => some (.leaf [])
    | .facts ts => refuteG F ks n b (ts ++ rest) cs
    | .cons ls => refuteG F ks n b rest (ls ++ cs)
    | .split bs => match fmCert F cs with
      | some c => some c
      | none => if b = 0 then none else
        (bs.mapM fun ts => refuteG F ks n (b - 1) (ts ++ rest) cs).map .br
    | .ite c t1 t2 => match fmCert F cs with
      | some w => some w
      | none => if b = 0 then none else do
        let h1 ← refuteG F ks n (b - 1)
          (c :: ((t1 :: rest).map (resolve c true resolveFuel)).map (substN (iteEqs c) substFuel))
          (cs.map (Lin.substE (iteEqs c)))
        let h2 ← refuteG F ks n (b - 1) (neg c :: (t2 :: rest).map (resolve c false resolveFuel)) cs
        some (.br [h1, h2])
    | .skolem x t =>
      if fresh x rest cs then refuteG F ks n b (t :: rest) cs
      else if fresh (x ++ "'") (t :: rest) cs then
        refuteG F ks n b (t.subst .int x (.ivar (x ++ "'")) :: rest) cs
      else refuteG F ks n b rest cs

/-- `refuteOb`, returning which fact list it used and its certificate. -/
def certOb (fs : List Tm) : Option (Bool × Cert) :=
  let eqs := fs.filterMap eqOf?
  let gs := (fs.filter fun t => (eqOf? t).isNone).map fun t => rowN rowFuel (substN eqs substFuel t)
  let rs := relevant gs
  if refute fmFuel (goalBinders rs) stepFuel splitFuel (goalFirst rs) [] then
    (refuteG fmFuel (goalBinders rs) stepFuel splitFuel (goalFirst rs) []).map fun c => (false, c)
  else (refuteG fmFuel (goalBinders rs) stepFuel splitFuel (goalFirst rs ++ divFacts rs) []).map
      fun c => (true, c)

/-- The certificate of obligation `i`, checked compiled before it is printed. -/
def certAt (cs : List Cmd) (i : Nat) : Option (Bool × Cert) :=
  let fs := (obligations cs).getD i []
  if isProbe fs then some (false, .leaf []) else
  match certOb fs with
  | some (d, c) => if refuteObC fs d c then some (d, c) else none
  | none => none

/-! ## Soundness -/

section Sound

variable (σ : Env)

theorem farkasSum_le : ∀ (w : List Nat) (cs : List Lin), (∀ l ∈ cs, l.eval σ ≤ 0) →
    (farkasSum w cs).eval σ ≤ 0
  | w :: ws, l :: ls, h => by
    have hl := h l (by simp)
    have ih := farkasSum_le ws ls (fun l' hl' => h l' (by simp [hl']))
    simp only [farkasSum]
    split
    · exact ih
    · rw [Lin.eval_add, Lin.eval_scale]
      have : (0 : Int) ≤ (w : Int) := Int.natCast_nonneg w
      nlinarith
  | [], _, _ => by simp [farkasSum, Lin.eval, sumCs]
  | _ :: _, [], _ => by simp [farkasSum, Lin.eval, sumCs]

theorem farkas_sound {w : List Nat} {cs : List Lin} (h : farkas w cs = true)
    (hc : ∀ l ∈ cs, l.eval σ ≤ 0) : False := by
  have hle := farkasSum_le σ w cs hc
  rw [← Lin.eval_norm] at hle
  simp only [farkas, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
  generalize (farkasSum w cs).norm = l at h hle
  simp only [Lin.eval, h.1, sumCs] at hle
  omega

theorem sumCs_substN {eqs : List (Tm × Tm)} (he : ∀ e ∈ eqs, e.1.eval σ = e.2.eval σ) :
    ∀ l : List (Tm × Int), sumCs σ (l.map fun p => (substN eqs substFuel p.1, p.2)) = sumCs σ l
  | [] => rfl
  | p :: ps => by
    simp only [List.map_cons, sumCs, substN_eval _ _ σ he, sumCs_substN he ps]

theorem Lin.eval_substE {eqs : List (Tm × Tm)} (he : ∀ e ∈ eqs, e.1.eval σ = e.2.eval σ) (l : Lin) :
    (l.substE eqs).eval σ = l.eval σ := by
  simp only [Lin.substE, Lin.eval_norm]
  simp only [Lin.eval, sumCs_substN σ he]

theorem mem_zip_of_mem {α β : Type} {as : List α} {bs : List β} (hl : as.length = bs.length) {a : α}
    (ha : a ∈ as) : ∃ b, (a, b) ∈ as.zip bs := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨bs[i]'(hl ▸ hi), by
    have : (as.zip bs)[i]'(by simp [hl] at hi ⊢; omega) = (as[i], bs[i]'(hl ▸ hi)) := by simp
    rw [← this]; exact List.getElem_mem _⟩

theorem refuteC_sound (ks : List String) : ∀ (n : Nat) (σ : Env) (ts : List Tm) (cs : List Lin) (k : Cert),
    refuteC ks n ts cs k = true → (∀ t ∈ ts, t.Holds σ) → (∀ l ∈ cs, l.eval σ ≤ 0) → False
  | 0, _, _, _, _, h, _, _ => by simp [refuteC] at h
  | n + 1, σ, [], cs, k, h, _, hc => by
    cases k with
    | leaf w => exact farkas_sound σ (by simpa [refuteC] using h) hc
    | _ => simp [refuteC] at h
  | n + 1, σ, t :: rest, cs, k, h, ht, hc => by
    have hlater : ∀ k', refuteC ks n (rest ++ [t]) cs k' = true → False := fun k' h' =>
      refuteC_sound ks n σ _ cs k' h' (fun u hu => ht u (by simp at hu ⊢; tauto)) hc
    simp only [refuteC] at h
    have hst := step_sound σ ks t (ht t (by simp))
    have hr : ∀ u ∈ rest, u.Holds σ := fun u hu => ht u (by simp [hu])
    generalize step ks t = s at h hst
    cases s with
    | drop => exact refuteC_sound ks n σ rest cs k h hr hc
    | closed => exact hst
    | facts us => exact refuteC_sound ks n σ _ cs k h (List.forall_mem_append.2 ⟨hst, hr⟩) hc
    | cons ls => exact refuteC_sound ks n σ rest _ k h hr (List.forall_mem_append.2 ⟨hst, hc⟩)
    | split bs =>
      cases k with
      | leaf w => exact farkas_sound σ h hc
      | later k' => exact hlater k' h
      | keep _ _ => simp at h
      | br hs =>
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
        obtain ⟨us, hus, hall⟩ := hst
        obtain ⟨hh, hmem⟩ := mem_zip_of_mem h.1 hus
        exact refuteC_sound ks n σ _ cs hh (h.2 _ hmem) (List.forall_mem_append.2 ⟨hall, hr⟩) hc
    | ite c t1 t2 =>
      cases k with
      | leaf w => exact farkas_sound σ h hc
      | later k' => exact hlater k' h
      | keep _ _ => simp at h
      | br hs =>
        match hs, h with
        | [h1, h2], h =>
          rw [Bool.and_eq_true] at h
          rcases ite_cases σ hst hr with ⟨hc1, hts⟩ | hts
          · refine refuteC_sound ks n σ _ _ h1 h.1 hts fun l hl => ?_
            obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
            rw [Lin.eval_substE σ (iteEqs_sound σ c hc1)]
            exact hc l' hl'
          · exact refuteC_sound ks n σ _ cs h2 h.2 hts hc
        | [], h | [_], h | _ :: _ :: _ :: _, h => simp at h
    | skolem x u =>
      exact skolem_sound σ (refuteC ks n · cs k) (fun τ ts h => refuteC_sound ks n τ ts cs k h)
        h hst hr hc

theorem refuteObC_sound {fs : List Tm} {d : Bool} {c : Cert} (h : refuteObC fs d c = true) :
    ∀ σ : Env, ¬ ∀ t ∈ fs, t.Holds σ := by
  intro σ hσ
  have hall := refuteOb_facts σ hσ d
  simp only [refuteObC] at h
  split at h
  · exact refuteC_sound _ _ σ _ [] _ h (fun t ht => hall t (mem_keepMask _ _ ht)) (by simp)
  · exact refuteC_sound _ _ σ _ [] _ h hall (by simp)

end Sound

/-- **The discharge along certificates, one obligation at a time.** -/
theorem dischargeScript_of_certs (cs : List Cmd)
    (h : ∀ i < (obligations cs).length, ∃ d c, dischargeAtC cs i d c = true) : Valid cs := by
  intro fs hfs hp σ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfs
  obtain ⟨d, c, hc⟩ := h i hi
  simp only [dischargeAtC, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some, hp, Bool.false_or] at hc
  exact refuteObC_sound hc σ

end SolidCore.Verify.VC

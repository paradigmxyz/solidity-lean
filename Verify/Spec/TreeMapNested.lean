import Verify.Spec.TreeMap

/-!
# Nested mapping slots in tree specs

`tree_meets_map` (TreeMap.lean) knows the slots `m[a]` of mappings at literal slots. A mapping of
mappings at slot `n`, such as an ERC20 allowance `allowance[o][s]`, stores at
`solHash s (solHash o n)`, whose mapping slot is itself a hash. `NestedSlotsSeparated ms ns` is
the one hypothesis for both kinds: keccak256 is separated (injective, every image at least
`2 ^ 128`) on the preimages of `m[a]` for `m ∈ ms ++ ns` and of `n[b][a]` for `n ∈ ns`, for all
addresses `a` and `b`. It is `MapSlotsSeparated (ms ++ ns)` with the second level added and, like
it, a premise of the theorems that use it, never an axiom.

`nmap_inj_ln`, `nmap_inj_nn` and `nmap_ge_n` say when second-level slots are equal to others;
`hash_facts_nested` instantiates them for every pair of slot terms of the goal and the
hypotheses, beside `hash_facts`'s first-level instances. `tree_meets_map2` is `tree_meets_map` with
both: it proves `TreeMeetsFixed` from `NestedSlotsSeparated ms ns` with no other input, or fails.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- keccak256 is separated on the slots of `m[a]` for `m ∈ ms ++ ns` and of `n[b][a]` for `n ∈ ns`,
for all addresses `a` and `b`. -/
def NestedSlotsSeparated (ms ns : List Nat) : Prop :=
  TrustedBase.KeccakSeparated (fun x => ∃ a < 2 ^ 160,
    (∃ m ∈ ms ++ ns, x = TrustedBase.mappingPreimage a m) ∨
    ∃ b < 2 ^ 160, ∃ n ∈ ns, x = TrustedBase.mappingPreimage a (solHash b n))

/-- Equal preimages of two mapping slots have equal keys and equal mapping slots. -/
theorem mappingPreimage_inj {a b m n : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hm : m < 2 ^ 256) (hn : n < 2 ^ 256)
    (h : TrustedBase.mappingPreimage a m = TrustedBase.mappingPreimage b n) : a = b ∧ m = n := by
  unfold TrustedBase.mappingPreimage at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [length_wordBytes])
  have e1 := congrArg bytesWord h1
  have e2 := congrArg bytesWord h2
  rw [bytesWord_wordBytes, bytesWord_wordBytes] at e1 e2
  omega

/-- The first level of the nested hypothesis. -/
theorem NestedSlotsSeparated.flat {ms ns : List Nat} (h : NestedSlotsSeparated ms ns) :
    MapSlotsSeparated (ms ++ ns) :=
  h.mono fun _ ⟨a, ha, m, hm, hx⟩ => ⟨a, ha, .inl ⟨m, hm, hx⟩⟩

/-- A second-level slot is at least `2 ^ 128`. -/
theorem nmap_ge_n {ms ns : List Nat} (h : NestedSlotsSeparated ms ns) (n : Nat) (hn : n ∈ ns)
    (a c : Nat) : a < 2 ^ 160 → c < 2 ^ 160 → 2 ^ 128 ≤ solHash a (solHash c n) := by
  intro ha hc
  rw [solHash_eq a]
  exact h.2 _ ⟨a, ha, .inr ⟨c, hc, n, hn, rfl⟩⟩

/-- A first-level slot of a small mapping slot is no second-level slot. -/
theorem nmap_inj_ln {ms ns : List Nat} (h : NestedSlotsSeparated ms ns) (m n : Nat)
    (hm : m ∈ ms ++ ns) (hn : n ∈ ns) (hmw : m < 2 ^ 128) (a b c : Nat) :
    a < 2 ^ 160 → b < 2 ^ 160 → c < 2 ^ 160 → solHash a m = solHash b (solHash c n) → False := by
  intro ha hb hc he
  rw [solHash_eq a, solHash_eq b] at he
  have := h.1 _ _ ⟨a, ha, .inl ⟨m, hm, rfl⟩⟩ ⟨b, hb, .inr ⟨c, hc, n, hn, rfl⟩⟩ he
  obtain ⟨-, e⟩ := mappingPreimage_inj (by omega) (by omega) (by omega) (solHash_lt _ _) this
  have hge := map_ge' h.flat n (List.mem_append_right ms hn) c hc
  omega

/-- Two second-level slots are equal only for the same keys and mapping. -/
theorem nmap_inj_nn {ms ns : List Nat} (h : NestedSlotsSeparated ms ns) (n n' : Nat) (hn : n ∈ ns)
    (hn' : n' ∈ ns) (hnw : n < 2 ^ 256) (hnw' : n' < 2 ^ 256) (a b c d : Nat) :
    a < 2 ^ 160 → b < 2 ^ 160 → c < 2 ^ 160 → d < 2 ^ 160 →
      solHash a (solHash c n) = solHash b (solHash d n') → a = b ∧ c = d ∧ n = n' := by
  intro ha hb hc hd he
  rw [solHash_eq a, solHash_eq b] at he
  have := h.1 _ _ ⟨a, ha, .inr ⟨c, hc, n, hn, rfl⟩⟩ ⟨b, hb, .inr ⟨d, hd, n', hn', rfl⟩⟩ he
  obtain ⟨e1, e2⟩ := mappingPreimage_inj (by omega) (by omega) (solHash_lt _ _) (solHash_lt _ _) this
  obtain ⟨e3, e4⟩ := map_inj' h.flat n n' (List.mem_append_right ms hn) (List.mem_append_right ms hn')
    hnw hnw' c d hc hd e2
  exact ⟨e1, e3, e4⟩

/-- A natural number's cast modulo an integer literal, back in the naturals. -/
theorem toNat_natCast_emod_ofNat (a N : Nat) [N.AtLeastTwo] :
    ((a : Int) % (OfNat.ofNat N : Int)).toNat = a % N := by
  rw [show (OfNat.ofNat N : Int) = ((N : Nat) : Int) from rfl, ← Int.natCast_emod, Int.toNat_natCast]

/-- A word's cast modulo `2 ^ 256`, back in the naturals. -/
theorem toNat_natCast_emod_word {a : Nat} (h : a < 2 ^ 256) :
    ((a : Int) % 115792089237316195423570985008687907853269984665640564039457584007913129639936).toNat = a := by
  omega

open Lean Meta Elab Tactic in
/-- `hash_facts_nested H hgn hln hnn`, with `H` the slot hash: for every second-level term
`H x (H c n)` of the goal and the hypotheses, `hgn n _ x c`; with every first-level term `H x' m`,
`hln m n _ _ _ x' x c`; with every other second-level term `H x' (H c' n')`,
`hnn n n' _ _ _ _ x x' c c'`. Each is an instance of a hypothesis; one whose side conditions
`decide` does not show is left out. -/
elab "hash_facts_nested " H:ident hgn:ident hln:ident hnn:ident : tactic => do
  let (He, es) ← withMainContext do pure (← getFVarFromUserName H.getId, ← goalAndHyps)
  let (ts, _) ← hashTerms He none es
  let isNested (t : Expr) : Bool := isSlotOf He t.appArg!
  for i in [0:ts.size] do
    let t := ts[i]!
    if !isNested t then continue
    withMainContext do
      let x ← Term.exprToSyntax t.appFn!.appArg!
      let c ← Term.exprToSyntax t.appArg!.appFn!.appArg!
      let n ← Term.exprToSyntax t.appArg!.appArg!
      evalTactic (← `(tactic| try have := $hgn $n (by decide) $x $c))
    for j in [0:ts.size] do
      if i == j then continue
      let u := ts[j]!
      withMainContext do
        let x ← Term.exprToSyntax t.appFn!.appArg!
        let c ← Term.exprToSyntax t.appArg!.appFn!.appArg!
        let n ← Term.exprToSyntax t.appArg!.appArg!
        let x2 ← Term.exprToSyntax u.appFn!.appArg!
        if isNested u then
          if i < j then
            let c2 ← Term.exprToSyntax u.appArg!.appFn!.appArg!
            let n2 ← Term.exprToSyntax u.appArg!.appArg!
            evalTactic (← `(tactic| try have := $hnn $n $n2 (by decide) (by decide) (by decide) (by decide) $x $x2 $c $c2))
        else
          let m ← Term.exprToSyntax u.appArg!
          evalTactic (← `(tactic| try have := $hln $m $n (by decide) (by decide) (by decide) $x2 $x $c))

open Lean Meta Elab Tactic in
/-- Whether `ty` is, up to reducible unfolding, a clause `∀ x : Nat, x < b → P x` (or `x ≤ b`), as
`inst_foralls` and `inst_forall_lits` instantiate. -/
def isBoundedForall (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isForall && ty.bindingDomain!.isConstOf `Nat && ty.bindingBody!.hasLooseBVars &&
    ty.bindingBody!.isForall && (ty.bindingBody!.bindingDomain!.isAppOfArity `LT.lt 4 ||
      ty.bindingBody!.bindingDomain!.isAppOfArity `LE.le 4)

open Lean Meta Elab Tactic in
/-- `f a` for every clause `f` of `fs` and every `a` of `as` (as the term `arg a`), its bound
discharged by `omega`; an instance whose bound `omega` does not show is left out. -/
def instClauses {α : Type} (fs : Array FVarId) (as : Array α) (arg : α → TacticM (TSyntax `term)) :
    TacticM Unit := do
  for f in fs do
    for a in as do
      withMainContext do
        let fe ← Term.exprToSyntax (mkFVar f)
        let ae ← arg a
        evalTactic (← `(tactic| first | have := $fe $ae (by omega) | skip))

open Lean Meta Elab Tactic in
/-- `inst_foralls`: split every conjunction among the hypotheses, then instantiate every hypothesis
`∀ x : Nat, x < b → P x` (a quantified clause of an invariant, such as `allowance[address(0)][s] == 0`
for every address `s`) at every natural-number variable of the context, its bound discharged by
`omega`. Each instance is a consequence of a hypothesis; one whose bound `omega` does not show is
left out. -/
elab "inst_foralls" : tactic => do
  -- Split every conjunction once (its parts too), keeping the original.
  let done ← IO.mkRef (#[] : Array FVarId)
  for _ in [0:64] do
    let next ← withMainContext do
      let seen ← done.get
      let mut r := none
      for d in (← getLCtx) do
        if d.isImplementationDetail || seen.contains d.fvarId then continue
        if (← instantiateMVars d.type).isAppOfArity `And 2 then
          r := some d.fvarId
          break
      pure r
    let some h := next | break
    done.modify (·.push h)
    withMainContext do
      let hs ← Term.exprToSyntax (mkFVar h)
      evalTactic (← `(tactic| have := ($hs).1))
      evalTactic (← `(tactic| have := ($hs).2))
  let (fs, vs) ← withMainContext do
    let mut fs := #[]
    let mut vs := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if (← isBoundedForall (← instantiateMVars d.type)) then
        fs := fs.push d.fvarId
      else if (← instantiateMVars d.type).isConstOf `Nat then
        vs := vs.push d.fvarId
    pure (fs, vs)
  instClauses fs vs fun v => Term.exprToSyntax (mkFVar v)

open Lean Meta Elab Tactic in
/-- `hash_bounds H s hlt hs`: for every slot term `H x y` of the goal and the hypotheses,
`hlt x y : H x y < 2 ^ 256`, and for every storage read `s x`, `hs x : s x < 2 ^ 256`: word bounds only, no
implication, so `omega` stays linear in them. -/
elab "hash_bounds " H:ident s:ident hlt:ident hs:ident : tactic => do
  let (ts, ss) ← slotTerms H s
  hashBounds ts ss hlt hs fun _ _ => pure ()

open Lean Meta Elab Tactic in
/-- `hash_eqs H hinj hge hgn hln hnn`: for every hypothesis that equates a slot term `H x y` with
another one (a branch of the tree or of the spec where two slots coincide), the consequence the
separation gives: the keys and mapping slots are equal (`hinj`, `hnn`) or there is no such branch
(`hln`); and for one equating a slot term with anything else, that the slot is at least `2 ^ 128`
(`hge`, `hgn`). Address bounds are discharged by `omega`, membership by `decide`; an instance
whose side conditions do not hold is left out. Only equalities present in the context are used, so
the facts grow with the branch, not with the square of the slot terms. -/
elab "hash_eqs " H:ident hinj:ident hge:ident hgn:ident hln:ident hnn:ident : tactic => do
  let eqs ← withMainContext do
    let He ← getFVarFromUserName H.getId
    let mut acc := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, l, r) := ty.eq? then
        if (isSlotOf He l || isSlotOf He r) && !ty.hasLooseBVars then acc := acc.push (d.fvarId, l, r)
    pure (acc, He)
  let (eqs, He) := eqs
  let isH := isSlotOf He
  let isN (t : Expr) : Bool := isH t && isH t.appArg!
  for (h, l, r) in eqs do
    withMainContext do
      let hs ← Term.exprToSyntax (mkFVar h)
      let k (t : Expr) := Term.exprToSyntax t.appFn!.appArg!
      let m (t : Expr) := Term.exprToSyntax t.appArg!
      let c (t : Expr) := Term.exprToSyntax t.appArg!.appFn!.appArg!
      let n (t : Expr) := Term.exprToSyntax t.appArg!.appArg!
      if isH l && isH r then
        if !isN l && !isN r then
          let (x, y, x2, y2) := (← k l, ← m l, ← k r, ← m r)
          evalTactic (← `(tactic| try (have e := $hinj $y $y2 (by decide) (by decide) (by decide) (by decide) $x $x2 (by omega) (by omega) $hs; have := e.1; have := e.2; clear e)))
        else if !isN l && isN r then
          let (x, y, x2, c2, n2) := (← k l, ← m l, ← k r, ← c r, ← n r)
          evalTactic (← `(tactic| try have := $hln $y $n2 (by decide) (by decide) (by decide) $x $x2 $c2 (by omega) (by omega) (by omega) $hs))
        else if isN l && !isN r then
          let (x, c1, n1, x2, y2) := (← k l, ← c l, ← n l, ← k r, ← m r)
          evalTactic (← `(tactic| try have := $hln $y2 $n1 (by decide) (by decide) (by decide) $x2 $x $c1 (by omega) (by omega) (by omega) ($hs).symm))
        else
          let (x, c1, n1, x2, c2, n2) := (← k l, ← c l, ← n l, ← k r, ← c r, ← n r)
          evalTactic (← `(tactic| try (have e := $hnn $n1 $n2 (by decide) (by decide) (by decide) (by decide) $x $x2 $c1 $c2 (by omega) (by omega) (by omega) (by omega) $hs; have := e.1; have := e.2.1; have := e.2.2; clear e)))
      for t in [l, r] do
        if isN t then
          let (x, c1, n1) := (← k t, ← c t, ← n t)
          evalTactic (← `(tactic| try have := $hgn $n1 (by decide) $x $c1 (by omega) (by omega)))
        else if isH t then
          let (x, y) := (← k t, ← m t)
          evalTactic (← `(tactic| try have := $hge $y (by decide) $x (by omega)))

/-- The links after the decoding of `tree_meets_map2` and `tree_meets_map2_on`: the separation
lemmas of both levels from `hsep`, the slot hash's bound `hlt` and `hkec`. -/
def nestedLinks (hsep : Lean.TSyntax `term) : Lean.MacroM (Array (Lean.TSyntax `tactic)) := return #[
  ← `(tactic| have hinj := map_inj' (NestedSlotsSeparated.flat $hsep)),
  ← `(tactic| have hge := map_ge' (NestedSlotsSeparated.flat $hsep)),
  ← `(tactic| have hgn := nmap_ge_n $hsep), ← `(tactic| have hln := nmap_inj_ln $hsep),
  ← `(tactic| have hnn := nmap_inj_nn $hsep), ← `(tactic| have hlt := solHash_lt'),
  ← `(tactic| have hkec := keccak_solHash)]

/-- `invBase` with the string comparisons of a nested spec's terms. -/
def nestedInv : Lean.MacroM (Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  return (← invBase) ++ #[← `(Lean.Parser.Tactic.simpLemma| String.reduceBEq), ← `(Lean.Parser.Tactic.simpLemma| Bool.false_eq_true)]

/-- The steps of `tree_meets_map2` and `tree_meets_map2_on` after `meetsSteps`, each
`allGoals lenient` but the last: split the goals, cast the words back to naturals, instantiate the
invariants' quantified clauses (then `extra`), bound the slot terms and close each case with
`hash_eqs`. -/
def nestedSteps (lenient : Bool) (extra : Array (Lean.TSyntax `tactic)) :
    Lean.MacroM (Array (Lean.TSyntax `tactic)) := do
  let step := allGoals lenient
  return #[← splitGoals lenient,
    ← step (← `(tactic| (try simp only [toNat_natCast_emod_ofNat] at hinv ⊢))),
    ← step (← `(tactic| (try simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
      toNat_natCast_emod_word, toNat_natCast_emod, Int.toNat_natCast, Nat.cast_inj, Nat.cast_le, Nat.cast_lt] at hinv ⊢))),
    ← step (← `(tactic| inst_foralls))] ++ extra ++ #[
    ← step (← `(tactic| (try simp (disch := omega) only [toNat_natCast_emod_word, Int.toNat_natCast, Nat.cast_inj] at *))),
    ← step (← `(tactic| hash_bounds H s hlt hs)),
    ← `(tactic| all_goals ((try split_ifs) <;> (try simp only [Nat.cast_inj] at *) <;> (hash_eqs H hinj hge hgn hln hnn; (try subst_vars); first | contradiction | omega)))]

/-- `tree_meets_map2 [defs] hsep` is `tree_meets_map` for functions that also read and write
mappings of mappings keyed by addresses at the slots `ns`, from `hsep : NestedSlotsSeparated ms ns`:
`hash_facts` instantiates the first level (`map_inj`, `map_ge` of `ms ++ ns`) and
`hash_facts_nested` the second. A case it cannot close stays an error: it never leaves a `sorry`. -/
macro "tree_meets_map2" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => do
  seqTactics (#[← `(tactic| intro args s iargs pre hl hargs hs hdec hst ht hreq hinv),
    ← `(tactic| simp only [Nat.reducePow] at hs),
    ← chainTactics ((← decodeArgs ds) ++ (← nestedLinks hsep) ++ #[
      ← `(tactic| generalize solHash = H at hinj hge hgn hln hnn hlt hkec ⊢),
      ← `(tactic| refine ⟨fun hsucc => ?_, fun hne => ?_⟩)])] ++
    (← meetsSteps ds false false (← nestedInv)) ++ (← nestedSteps false #[]))

/-- info: 'SolidCore.Spec.nmap_inj_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nmap_inj_nn

end SolidCore.Spec

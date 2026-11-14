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
  let ts ← withMainContext do
    let He ← getFVarFromUserName H.getId
    let mut es := #[← instantiateMVars (← getMainTarget)]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      es := es.push (← instantiateMVars d.type)
    let tr ← IO.mkRef (#[] : Array Expr)
    for e in es do
      e.forEachWhere (fun t => t.getAppFn == He && t.getAppNumArgs == 2 && !t.hasLooseBVars)
        fun t => tr.modify fun a => if a.contains t then a else a.push t
    pure (← tr.get, He)
  let (ts, He) := ts
  let isNested (t : Expr) : Bool :=
    let y := t.appArg!
    y.getAppFn == He && y.getAppNumArgs == 2
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
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isForall && ty.bindingDomain!.isConstOf `Nat && ty.bindingBody!.hasLooseBVars &&
          ty.bindingBody!.isForall && (ty.bindingBody!.bindingDomain!.isAppOfArity `LT.lt 4 ||
            ty.bindingBody!.bindingDomain!.isAppOfArity `LE.le 4) then
        fs := fs.push d.fvarId
      else if (← instantiateMVars d.type).isConstOf `Nat then
        vs := vs.push d.fvarId
    pure (fs, vs)
  for f in fs do
    for v in vs do
      withMainContext do
        let fe ← Term.exprToSyntax (mkFVar f)
        let ve ← Term.exprToSyntax (mkFVar v)
        evalTactic (← `(tactic| first | have := $fe $ve (by omega) | skip))


open Lean Meta Elab Tactic in
/-- `hash_bounds H s hlt hs`: for every slot term `H x y` of the goal and the hypotheses,
`hlt x y : H x y < 2 ^ 256`, and for every storage read `s x`, `hs x : s x < 2 ^ 256`: word bounds only, no
implication, so `omega` stays linear in them. -/
elab "hash_bounds " H:ident s:ident hlt:ident hs:ident : tactic => do
  let (ts, ss) ← withMainContext do
    let He ← getFVarFromUserName H.getId
    let se ← getFVarFromUserName s.getId
    let mut es := #[← instantiateMVars (← getMainTarget)]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      es := es.push (← instantiateMVars d.type)
    let tr ← IO.mkRef (#[] : Array Expr)
    let sr ← IO.mkRef (#[] : Array Expr)
    for e in es do
      e.forEachWhere (fun t => t.getAppFn == He && t.getAppNumArgs == 2 && !t.hasLooseBVars)
        fun t => tr.modify fun a => if a.contains t then a else a.push t
      e.forEachWhere (fun t => t.isApp && t.appFn! == se && !t.hasLooseBVars)
        fun t => sr.modify fun a => if a.contains t.appArg! then a else a.push t.appArg!
    pure (← tr.get, ← sr.get)
  for t in ts do
    withMainContext do
      let x ← Term.exprToSyntax t.appFn!.appArg!
      let y ← Term.exprToSyntax t.appArg!
      evalTactic (← `(tactic| have := $hlt $x $y))
  for x in ss do
    withMainContext do
      let x ← Term.exprToSyntax x
      evalTactic (← `(tactic| try have := $hs $x))

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
    let isH (t : Expr) : Bool := t.getAppFn == He && t.getAppNumArgs == 2
    let mut acc := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, l, r) := ty.eq? then
        if (isH l || isH r) && !ty.hasLooseBVars then acc := acc.push (d.fvarId, l, r)
    pure (acc, He)
  let (eqs, He) := eqs
  let isH (t : Expr) : Bool := t.getAppFn == He && t.getAppNumArgs == 2
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

/-- `tree_meets_map2 [defs] hsep` is `tree_meets_map` for functions that also read and write
mappings of mappings keyed by addresses at the slots `ns`, from `hsep : NestedSlotsSeparated ms ns`:
`hash_facts` instantiates the first level (`map_inj`, `map_ge` of `ms ++ ns`) and
`hash_facts_nested` the second. A case it cannot close stays an error: it never leaves a `sorry`. -/
macro "tree_meets_map2" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => `(tactic| (
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv
  simp only [Nat.reducePow] at hs
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> (try omega) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true, Nat.reducePow] at hargs <;>
    simp only [$ds,*, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords, Ty.ofWord,
      bind, pure, Option.bind, Nat.reducePow] at hdec <;>
    split_ifs at hdec <;> simp only [Option.some.injEq, reduceCtorEq] at hdec <;>
    subst hdec <;>
    have hinj := map_inj' (NestedSlotsSeparated.flat $hsep) <;>
    have hge := map_ge' (NestedSlotsSeparated.flat $hsep) <;>
    have hgn := nmap_ge_n $hsep <;> have hln := nmap_inj_ln $hsep <;> have hnn := nmap_inj_nn $hsep <;>
    have hlt := solHash_lt' <;>
    have hkec := keccak_solHash <;>
    generalize solHash = H at hinj hge hgn hln hnn hlt hkec ⊢ <;>
    refine ⟨fun hsucc => ?_, fun hne => ?_⟩
  all_goals try (simp [$ds,*] at hne; done)
  all_goals simp only [$ds,*, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow] at hsucc ⊢
  all_goals simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not] at hsucc ⊢
  all_goals split_ifs at hsucc ⊢
  all_goals simp only [Bool.false_eq_true, Bool.true_eq_false, imp_false, not_true_eq_false,
    IsEmpty.forall_iff] at hsucc
  all_goals simp only [$ds,*, OByte.eval, WExpr.eval, Generic.wordSize, words, bytesWord, decodeWords, Ty.ofWord,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.drop_zero, List.take_succ_cons, List.take_zero, List.foldl_cons,
    List.foldl_nil, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceLT, ite_true, ite_false, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq,
    exists_eq_left', bind, pure, Option.bind, Ty.InRange, Nat.cast_ofNat, Nat.zero_add,
    Nat.reduceLeDiff] at hsucc ⊢
  all_goals try clear hsucc
  all_goals try refine ⟨?_, ?_⟩
  all_goals simp only [Bundle.satAll, Bundle.sat, $ds,*, List.getElem_cons_succ, List.getElem_cons_zero,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv,
    Env.cur, Env.bind, BinOp.apply, Ty.ofBits, toWord, List.getD_cons_zero, List.getD_cons_succ,
    List.lookup, hkec, ofProp_ne_zero, ite_true, ite_false, Bool.false_eq_true, Nat.zero_mod, hst,
    beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat,
    String.reduceBEq, Bool.false_eq_true] at hinv ⊢
  all_goals simp only [wordMod, Nat.reducePow] at hinv ⊢
  all_goals simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
    toNat_natCast_emod] at hinv ⊢
  all_goals simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hinv ⊢
  all_goals (repeat' (first | (apply And.intro) | intro))
  all_goals (try simp only [toNat_natCast_emod_ofNat] at hinv ⊢)
  all_goals (try simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
    toNat_natCast_emod_word, toNat_natCast_emod, Int.toNat_natCast, Nat.cast_inj, Nat.cast_le, Nat.cast_lt] at hinv ⊢)
  all_goals inst_foralls
  all_goals (try simp (disch := omega) only [toNat_natCast_emod_word, Int.toNat_natCast, Nat.cast_inj] at *)
  all_goals hash_bounds H s hlt hs
  all_goals ((try split_ifs) <;> (try simp only [Nat.cast_inj] at *) <;> (hash_eqs H hinj hge hgn hln hnn; (try subst_vars); first | contradiction | omega))))

/-- info: 'SolidCore.Spec.nmap_inj_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nmap_inj_nn

end SolidCore.Spec

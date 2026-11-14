import Verify.Spec.TreeMapNested

/-!
# Tree specs by cases on a tree's tests

`TreeMeetsFixedOn P` is `TreeMeetsFixed` on the evaluations that meet `P`. `TreeMeetsFixedOn.ite`
splits a tree's test into its two branches, each with the test's outcome added to `P`, so a spec of a
tree with many paths is proved as several smaller theorems, one per branch, each its own kernel
check. `tree_meets_map2_on` is `tree_meets_map2` for one branch: it reads the branch's tests from
`P` beside the other hypotheses. Nothing here is trusted: a case it cannot close is an error.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- `TreeMeetsFixed` on the evaluations that meet `P`. -/
def TreeMeetsFixedOn (P : Val → Prop) (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) :
    Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ a ∈ args, a < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    P ⟨args, s, solHash⟩ →
    Post b fs ctx pre pre.ghost (T.eval ⟨args, s, solHash⟩).obs iargs

theorem TreeMeetsFixedOn.fixed {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat} {T : Tree}
    (h : TreeMeetsFixedOn (fun _ => True) b fs ctx n T) : TreeMeetsFixed b fs ctx n T :=
  fun args s iargs pre hl hargs hs hdec hst ht hreq hinv =>
    h args s iargs pre hl hargs hs hdec hst ht hreq hinv trivial

/-- **A test splits a tree spec into its branches.** -/
theorem TreeMeetsFixedOn.ite {P : Val → Prop} {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat}
    {c : WExpr} {t e : Tree}
    (h1 : TreeMeetsFixedOn (fun ρ => P ρ ∧ c.eval ρ ≠ 0) b fs ctx n t)
    (h2 : TreeMeetsFixedOn (fun ρ => P ρ ∧ c.eval ρ = 0) b fs ctx n e) :
    TreeMeetsFixedOn P b fs ctx n (.ite c t e) := by
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hP
  simp only [Tree.eval]
  split
  · exact h2 args s iargs pre hl hargs hs hdec hst ht hreq hinv ⟨hP, by assumption⟩
  · exact h1 args s iargs pre hl hargs hs hdec hst ht hreq hinv ⟨hP, by assumption⟩

/-- info: 'SolidCore.Spec.TreeMeetsFixedOn.ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeMeetsFixedOn.ite

open Lean Meta Elab Tactic in
/-- `inst_forall_lits`: `inst_foralls` at the numerals of the context. It instantiates every hypothesis
`∀ x : Nat, x < b → P x` (a quantified clause of an invariant, such as `allowance[address(0)][s] == 0`
for every address `s`) at every numeral that is an argument of a two-argument application of a local
function (a slot hash `H k s`, such as the one of the caller's address), its bound discharged by
`omega`. Each instance is a consequence of a hypothesis; one whose bound `omega` does not show is
left out. -/
elab "inst_forall_lits" : tactic => do
  let lits ← IO.mkRef (#[] : Array Nat)
  let fs ← withMainContext do
    let mut fs := #[]
    let mut tys := #[← instantiateMVars (← getMainTarget)]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      tys := tys.push t
      let ty ← whnfR t
      if ty.isForall && ty.bindingDomain!.isConstOf `Nat && ty.bindingBody!.hasLooseBVars &&
          ty.bindingBody!.isForall && (ty.bindingBody!.bindingDomain!.isAppOfArity `LT.lt 4 ||
            ty.bindingBody!.bindingDomain!.isAppOfArity `LE.le 4) then
        fs := fs.push d.fvarId
    for t in tys do
      t.forEach fun e => do
        if let .app (.app (.fvar _) a) b := e then
          for x in [a, b] do
            if let some n := x.nat? then
              lits.modify fun acc => if acc.contains n then acc else acc.push n
    pure fs
  for f in fs do
    for n in (← lits.get) do
      withMainContext do
        let fe ← Term.exprToSyntax (mkFVar f)
        let ne := Syntax.mkNumLit (toString n)
        evalTactic (← `(tactic| first | have := $fe ($ne : Nat) (by omega) | skip))

/-- `tree_meets_map2` for one branch of a split tree (`TreeMeetsFixedOn`): `P`'s tests join the
hypotheses. -/
macro "tree_meets_map2_on" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => `(tactic| (
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hP
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
    generalize solHash = H at hinj hge hgn hln hnn hlt hkec hP ⊢ <;>
    simp only [true_and, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reducePow] at hP <;>
    refine ⟨fun hsucc => ?_, fun hne => ?_⟩
  all_goals try (simp [$ds,*] at hne; done)
  all_goals try (simp only [$ds,*, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow] at hsucc ⊢)
  all_goals try simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not, ne_eq] at hP
  all_goals try (simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not] at hsucc ⊢)
  all_goals try (first | split_ifs at hP hsucc ⊢ | split_ifs at hP ⊢ | split_ifs at hsucc ⊢)
  all_goals try (simp only [Bool.false_eq_true, Bool.true_eq_false, imp_false, not_true_eq_false,
    IsEmpty.forall_iff] at hsucc)
  all_goals try (simp only [$ds,*, OByte.eval, WExpr.eval, Generic.wordSize, words, bytesWord, decodeWords, Ty.ofWord,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.drop_zero, List.take_succ_cons, List.take_zero, List.foldl_cons,
    List.foldl_nil, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceLT, ite_true, ite_false, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq,
    exists_eq_left', bind, pure, Option.bind, Ty.InRange, Nat.cast_ofNat, Nat.zero_add,
    Nat.reduceLeDiff] at hsucc ⊢)
  all_goals try clear hsucc
  all_goals try refine ⟨?_, ?_⟩
  all_goals try (simp only [Bundle.satAll, Bundle.sat, $ds,*, List.getElem_cons_succ, List.getElem_cons_zero,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv,
    Env.cur, Env.bind, BinOp.apply, Ty.ofBits, toWord, List.getD_cons_zero, List.getD_cons_succ,
    List.lookup, hkec, ofProp_ne_zero, ite_true, ite_false, Bool.false_eq_true, Nat.zero_mod, hst,
    beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat,
    String.reduceBEq, Bool.false_eq_true] at hinv ⊢)
  all_goals try (simp only [wordMod, Nat.reducePow] at hinv ⊢)
  all_goals try (simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
    toNat_natCast_emod] at hinv ⊢)
  all_goals try (simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hinv ⊢)
  all_goals try ((repeat' (first | (apply And.intro) | intro)))
  all_goals try ((try simp only [toNat_natCast_emod_ofNat] at hinv ⊢))
  all_goals try ((try simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
    toNat_natCast_emod_word, toNat_natCast_emod, Int.toNat_natCast, Nat.cast_inj, Nat.cast_le, Nat.cast_lt] at hinv ⊢))
  all_goals try (inst_foralls)
  all_goals try (inst_forall_lits)
  all_goals try ((try simp (disch := omega) only [toNat_natCast_emod_word, Int.toNat_natCast, Nat.cast_inj] at *))
  all_goals try (hash_bounds H s hlt hs)
  all_goals ((try split_ifs) <;> (try simp only [Nat.cast_inj] at *) <;> (hash_eqs H hinj hge hgn hln hnn; (try subst_vars); first | contradiction | omega))))

end SolidCore.Spec

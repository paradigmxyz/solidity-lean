import Verify.Spec.Tree
import Verify.Spec.Hash

/-!
# Mapping slots in tree specs

`tree_meets` closes a function's cases by `omega` over words; a function that reads or writes a
mapping also needs to know which of its slots are equal. Those slots are SolidCore's
`solHash key slot`, which is the spec semantics' slot by `solHash_eq`. `MapSlotsSeparated ms` is
the one hypothesis: keccak256 is injective on the preimages of `m[a]` for the mapping slots
`m ∈ ms` and every address `a`, with images at least `2 ^ 128` (so apart from the scalar slots).
`map_inj` and `map_ge` give `omega` what it needs, and `hash_facts` adds their instances for
every slot term of the goal and the hypotheses. `tree_meets_map` is `tree_meets_fixed` for such
functions: it proves `TreeMeetsFixed` from `MapSlotsSeparated ms` with no other input.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- keccak256 is separated on the slots of `m[a]`, for every mapping slot `m ∈ ms` and every
address `a`. -/
def MapSlotsSeparated (ms : List Nat) : Prop :=
  TrustedBase.KeccakSeparated
    (fun x => ∃ a < 2 ^ 160, ∃ m ∈ ms, x = TrustedBase.mappingPreimage a m)

theorem MapSlotsSeparated.slots {ms : List Nat} (h : MapSlotsSeparated ms) {m : Nat}
    (hm : m ∈ ms) : SlotsSeparated m :=
  h.mono fun _ ⟨a, ha, hx⟩ => ⟨a, ha, m, hm, hx⟩

/-- One mapping's separation is `SlotsSeparated`. -/
theorem mapSlotsSeparated_singleton (m : Nat) : MapSlotsSeparated [m] ↔ SlotsSeparated m := by
  unfold MapSlotsSeparated SlotsSeparated
  constructor
  · intro h; exact h.mono fun _ ⟨a, ha, hx⟩ => ⟨a, ha, m, List.mem_singleton_self m, hx⟩
  · intro h
    refine h.mono fun x ⟨a, ha, n, hn, hx⟩ => ⟨a, ha, ?_⟩
    rw [List.mem_singleton] at hn
    exact hn ▸ hx

/-- Two slots of separated mappings are equal only for the same key and mapping. -/
theorem map_inj {ms : List Nat} (h : MapSlotsSeparated ms) {m n : Nat} (hm : m ∈ ms) (hn : n ∈ ms)
    (hmw : m < 2 ^ 256) (hnw : n < 2 ^ 256) (a b : Nat) :
    a < 2 ^ 160 → b < 2 ^ 160 → solHash a m = solHash b n → a = b ∧ m = n := by
  intro ha hb he
  rw [solHash_eq, solHash_eq] at he
  have := h.1 _ _ ⟨a, ha, m, hm, rfl⟩ ⟨b, hb, n, hn, rfl⟩ he
  unfold TrustedBase.mappingPreimage at this
  obtain ⟨h1, h2⟩ := List.append_inj this (by simp [length_wordBytes])
  have e1 := congrArg bytesWord h1
  have e2 := congrArg bytesWord h2
  rw [bytesWord_wordBytes, bytesWord_wordBytes] at e1 e2
  omega

/-- A slot of a separated mapping is at least `2 ^ 128`. -/
theorem map_ge {ms : List Nat} (h : MapSlotsSeparated ms) {m : Nat} (hm : m ∈ ms) (a : Nat) :
    a < 2 ^ 160 → 2 ^ 128 ≤ solHash a m := by
  intro ha
  rw [solHash_eq]
  exact h.2 _ ⟨a, ha, m, hm, rfl⟩

theorem solHash_lt' (a b : Nat) :
    solHash a b < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  solHash_lt a b

theorem keccak_solHash (k s : Nat) : keccakWord (wordBytes k ++ wordBytes s) = solHash k s :=
  (solHash_eq k s).symm

theorem toNat_natCast_emod {a n : Nat} (h : a < n) : ((a : Int) % (n : Int)).toNat = a := by
  rw [← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt h]

theorem toNat_ofNat_emod (a n : Nat) [a.AtLeastTwo] :
    ((OfNat.ofNat a : Int) % (n : Int)).toNat = a % n := by
  rw [show (OfNat.ofNat a : Int) = ((a : Nat) : Int) from rfl, ← Int.natCast_emod, Int.toNat_natCast]

theorem toNat_zero_emod (n : Nat) : ((0 : Int) % (n : Int)).toNat = 0 := by simp
theorem toNat_one_emod (n : Nat) : ((1 : Int) % (n : Int)).toNat = 1 % n := by
  rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, ← Int.natCast_emod, Int.toNat_natCast]

theorem ite_mod_nat {P : Prop} [Decidable P] (a b n : Nat) :
    (if P then a else b) % n = if P then a % n else b % n := by split <;> rfl

theorem ite10_eq_zero_iff {P : Prop} [Decidable P] : ((if P then 1 else 0) : Nat) = 0 ↔ ¬ P := by
  split <;> simp_all

/-- An address-ranged quantifier over integers is one over naturals. -/
theorem forall_int_range {P : Int → Prop} (b : Nat) :
    (∀ v : Int, 0 ≤ v ∧ v < 2 ^ b → P v) ↔ ∀ n : Nat, n < 2 ^ b → P n := by
  constructor
  · intro h n hn; exact h n ⟨Int.natCast_nonneg n, by exact_mod_cast hn⟩
  · intro h v hv
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hv.1
    exact h n (by exact_mod_cast hv.2)

/-- `map_inj` for any two of the mappings, as `hash_facts` instantiates it. -/
theorem map_inj' {ms : List Nat} (h : MapSlotsSeparated ms) (m n : Nat) (hm : m ∈ ms) (hn : n ∈ ms)
    (hmw : m < 2 ^ 256) (hnw : n < 2 ^ 256) (a b : Nat) :
    a < 2 ^ 160 → b < 2 ^ 160 → solHash a m = solHash b n → a = b ∧ m = n :=
  map_inj h hm hn hmw hnw a b

theorem map_ge' {ms : List Nat} (h : MapSlotsSeparated ms) (m : Nat) (hm : m ∈ ms) (a : Nat) :
    a < 2 ^ 160 → 2 ^ 128 ≤ solHash a m :=
  map_ge h hm a

open Lean Meta Elab Tactic in
/-- `hash_facts H s hinj hge hlt hs`, with `H` the slot hash (generalized from `solHash`) and `s`
the storage: for every term `H x y` of the goal and the hypotheses, `hlt x y : H x y < 2 ^ 256`
and, when `decide` shows `y` is one of the separated mappings, `hge y _ x : x < 2 ^ 160 →
2 ^ 128 ≤ H x y` and, with every other such `H x' y'`, `hinj y y' _ _ _ _ x x' : x < 2 ^ 160 →
x' < 2 ^ 160 → H x y = H x' y' → x = x' ∧ y = y'`; and `hs x : s x < 2 ^ 256` for every
term `s x`. Each is an instance of a hypothesis; one whose side conditions `decide` does not show
is left out. -/
elab "hash_facts " H:ident s:ident hinj:ident hge:ident hlt:ident hs:ident : tactic => do
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
      evalTactic (← `(tactic| try have := $hge $y (by decide) $x))
  for x in ss do
    withMainContext do
      let x ← Term.exprToSyntax x
      evalTactic (← `(tactic| try have := $hs $x))
  for i in [0:ts.size] do
    for j in [i+1:ts.size] do
      withMainContext do
        let x1 ← Term.exprToSyntax ts[i]!.appFn!.appArg!
        let y1 ← Term.exprToSyntax ts[i]!.appArg!
        let x2 ← Term.exprToSyntax ts[j]!.appFn!.appArg!
        let y2 ← Term.exprToSyntax ts[j]!.appArg!
        evalTactic (← `(tactic| try have := $hinj $y1 $y2 (by decide) (by decide) (by decide) (by decide) $x1 $x2))


/-- \`tree_meets_map [defs] hsep\` proves \`TreeMeetsFixed b fs ctx n T\` for a function of at most eight
parameters that reads and writes mappings keyed by addresses at the slots \`ms\`, from
\`hsep : MapSlotsSeparated ms\`, unfolding \`defs\` (the tree, the spec bundle, the function's spec and
the call context). It decodes the argument words, generalizes the slot hash \`solHash\` to a
variable \`H\` (so no step evaluates keccak256), evaluates the tree and the spec's terms, splits
every branch, and closes each case by \`omega\` with \`hash_facts\`'s instances of \`map_inj\`,
\`map_ge\` and the word bounds. A case it cannot close stays an error: it never leaves a \`sorry\`. -/
macro "tree_meets_map" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => `(tactic| (
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
    have hinj := map_inj' $hsep <;> have hge := map_ge' $hsep <;> have hlt := solHash_lt' <;>
    have hkec := keccak_solHash <;>
    generalize solHash = H at hinj hge hlt hkec ⊢ <;>
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
    beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat] at hinv ⊢
  all_goals simp only [wordMod, Nat.reducePow] at hinv ⊢
  all_goals simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
    toNat_natCast_emod] at hinv ⊢
  all_goals simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hinv ⊢
  all_goals (repeat' (first | (apply And.intro) | intro))
  all_goals (hash_facts H s hinj hge hlt hs; split_ifs <;> omega)))

end SolidCore.Spec

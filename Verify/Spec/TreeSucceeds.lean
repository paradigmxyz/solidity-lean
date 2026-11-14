import Verify.Spec.TreeMap

/-!
# Succeeds-if conditions of the erased tree

\`TreeMeets\` (\`Verify.Spec.Tree\`) asks the tree's observable to meet a function spec's \`Post\`, whose
second part is the spec's succeeds-if conditions: from a pre-state meeting them, the call succeeds.
\`tree_meets\` proves the first part (the ensures and the invariants on success); this file proves
the second apart, as \`TreeSucceeds\`, so that a spec with succeeds-if conditions is proved of its
tree by two steps the kernel checks:

* \`TreeMeets b fs.noSucc ctx n T\` (the spec without its succeeds-if conditions, by \`tree_meets\`,
  or \`TreeMeetsFixed\` by \`tree_meets_fixed\` and \`tree_meets_map\`);
* \`TreeSucceeds b fs ctx n T\` (by \`tree_succeeds\` or, for a function reading mappings, by
  \`tree_succeeds_map\` from \`MapSlotsSeparated\`);

and \`treeMeets_of_succeeds\` (\`treeMeetsFixed_of_succeeds\`) puts them together.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- What a function's succeeds-if conditions ask of its erased tree: from every pre-state meeting
the precondition, the invariants and the succeeds-if conditions, the tree succeeds. -/
def TreeSucceeds (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) : Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ a ∈ args, a < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    b.satAll fs.succeedsIf (mkEnv ctx iargs [] pre pre) →
    (T.eval ⟨args, s, solHash⟩).obs.success = true

/-- No mapping slots: nothing to separate. -/
theorem mapSlotsSeparated_nil : MapSlotsSeparated [] :=
  TrustedBase.keccakSeparated_empty.mono fun _ ⟨_, _, _, hm, _⟩ => by simp at hm

/-- The function spec without its succeeds-if conditions. -/
def FnSpec.noSucc (fs : FnSpec) : FnSpec := { fs with succeedsIf := [] }

theorem treeMeets_of_succeeds {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat} {T : Tree}
    (h : TreeMeets b fs.noSucc ctx n T) (hs : TreeSucceeds b fs ctx n T) : TreeMeets b fs ctx n T := by
  intro args s iargs pre g' hl ha hs' hd hst ht hr hi
  exact ⟨(h args s iargs pre g' hl ha hs' hd hst ht hr hi).1,
    fun _ hsat => hs args s iargs pre hl ha hs' hd hst ht hr hi hsat⟩

theorem treeMeetsFixed_of_succeeds {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat} {T : Tree}
    (h : TreeMeetsFixed b fs.noSucc ctx n T) (hs : TreeSucceeds b fs ctx n T) :
    TreeMeetsFixed b fs ctx n T := by
  intro args s iargs pre hl ha hs' hd hst ht hr hi
  exact ⟨(h args s iargs pre hl ha hs' hd hst ht hr hi).1,
    fun _ hsat => hs args s iargs pre hl ha hs' hd hst ht hr hi hsat⟩

/-- \`tree_succeeds [defs]\` proves \`TreeSucceeds b fs ctx n T\` for a function of at most eight
parameters that reads no mapping: it decodes the argument words, evaluates the tree and the
succeeds-if terms, splits every branch and closes each by \`omega\`. -/
macro "tree_succeeds" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hsi
  simp only [Nat.reducePow] at hs
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> (try omega) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true, Nat.reducePow] at hargs <;>
    simp only [$ds,*, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords, Ty.ofWord,
      bind, pure, Option.bind, Nat.reducePow] at hdec <;>
    split_ifs at hdec <;> simp only [Option.some.injEq, reduceCtorEq] at hdec <;>
    subst hdec
  all_goals simp only [$ds,*, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow]
  all_goals simp (disch := simp only [hargs, hs, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not]
  all_goals simp only [Bundle.satAll, Bundle.sat, $ds,*, List.getElem_cons_succ, List.getElem_cons_zero,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv,
    Env.cur, Env.bind, BinOp.apply, Ty.ofBits, toWord, List.getD_cons_zero, List.getD_cons_succ,
    List.lookup, ofProp_ne_zero, ite_true, ite_false, Bool.false_eq_true, Nat.zero_mod, hst,
    beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat, Int.reducePow] at hsi
  all_goals simp only [wordMod, Nat.reducePow] at hsi
  all_goals simp (disch := first | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hsi
  all_goals ((try split_ifs) <;> (try rfl) <;> first | omega | (simp_all; done) | (simp_all; omega))))

/-- \`tree_succeeds_map [defs] hsep\`: \`tree_succeeds\` for a function that reads mappings keyed by
addresses at the slots \`ms\`, from \`hsep : MapSlotsSeparated ms\`, as \`tree_meets_map\` does. -/
macro "tree_succeeds_map" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => `(tactic| (
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hsi
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
    generalize solHash = H at hinj hge hlt hkec ⊢
  all_goals simp only [$ds,*, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow]
  all_goals simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not]
  all_goals simp only [Bundle.satAll, Bundle.sat, $ds,*, List.getElem_cons_succ, List.getElem_cons_zero,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv,
    Env.cur, Env.bind, BinOp.apply, Ty.ofBits, toWord, List.getD_cons_zero, List.getD_cons_succ,
    List.lookup, hkec, ofProp_ne_zero, ite_true, ite_false, Bool.false_eq_true, Nat.zero_mod, hst,
    beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat, Int.reducePow] at hsi
  all_goals simp only [wordMod, Nat.reducePow] at hsi
  all_goals simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hsi
  all_goals ((try split_ifs) <;> (try rfl) <;> first | (hash_facts H s hinj hge hlt hs; omega) |
    (hash_facts H s hinj hge hlt hs; simp_all; done) | (hash_facts H s hinj hge hlt hs; simp_all; omega))))

/-- \`tree_meets_map' [defs] hsep\`: \`tree_meets_map\`, with each simplification step allowed to make
no progress (a spec with no invariants, or a goal a step leaves alone), as \`spec_connect\` uses it for
a spec whose succeeds-if conditions \`tree_succeeds_map\` proves apart. -/
macro "tree_meets_map'" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => `(tactic| (
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
  all_goals try (simp only [$ds,*, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow] at hsucc ⊢)
  all_goals try (simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not] at hsucc ⊢)
  all_goals try (split_ifs at hsucc ⊢)
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
    beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat] at hinv ⊢)
  all_goals try (simp only [wordMod, Nat.reducePow] at hinv ⊢)
  all_goals try (simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
    toNat_natCast_emod] at hinv ⊢)
  all_goals try (simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hinv ⊢)
  all_goals (repeat' (first | (apply And.intro) | intro))
  all_goals (hash_facts H s hinj hge hlt hs; (try split_ifs) <;> first | omega | (simp_all; done) | (simp_all; omega))))

end SolidCore.Spec

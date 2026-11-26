import Verify.Spec.TreeMap

/-!
# Succeeds-if conditions of the erased tree

`TreeMeets` (`Verify.Spec.Tree`) asks the tree's observable to meet a function spec's `Post`, whose
second part is the spec's succeeds-if conditions: from a pre-state meeting them, the call succeeds.
`tree_meets` proves the first part (the ensures and the invariants on success); this file proves
the second apart, as `TreeSucceeds`, so that a spec with succeeds-if conditions is proved of its
tree by two steps the kernel checks:

* `TreeMeets b fs.noSucc ctx n T` (the spec without its succeeds-if conditions, by `tree_meets`,
  or `TreeMeetsFixed` by `tree_meets_fixed` and `tree_meets_map`);
* `TreeSucceeds b fs ctx n T` (by `tree_succeeds` or, for a function reading mappings, by
  `tree_succeeds_map` from `MapSlotsSeparated`);

and `treeMeets_of_succeeds` (`treeMeetsFixed_of_succeeds`) puts them together.
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
    (T.eval ⟨args, s, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs.success = true

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

/-- What `tree_succeeds` and `tree_succeeds_map` do after their case split: evaluate the tree and
the succeeds-if terms `hsi`, reducing each word mod `2 ^ 256`; with `map`, by the slot hash's bound
`hlt` and `hkec` too. -/
def succeedsSteps (ds : Lean.Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") (map : Bool) :
    Lean.MacroM (Array (Lean.TSyntax `tactic)) := do
  let mut bounds := #[← `(Lean.Parser.Tactic.simpLemma| Nat.reduceLT)]
  let mut lookup := #[← `(Lean.Parser.Tactic.simpLemma| List.lookup)]
  let mut disch ← `(tactic| first | exact hs _ | omega)
  if map then
    bounds := #[← `(Lean.Parser.Tactic.simpLemma| hlt)] ++ bounds
    lookup := lookup.push (← `(Lean.Parser.Tactic.simpLemma| hkec))
    disch ← `(tactic| first | exact hlt _ _ | exact hs _ | omega)
  return #[
    ← `(tactic| all_goals simp only [$ds,*, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
      Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow]),
    ← `(tactic| all_goals simp (disch := simp only [hargs, hs, $[$bounds],*]) only [Nat.mod_eq_of_lt, ite_mod_nat,
      Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not]),
    ← `(tactic| all_goals simp only [Bundle.satAll, Bundle.sat, $ds,*, List.getElem_cons_succ, List.getElem_cons_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv,
      Env.cur, Env.bind, BinOp.apply, Ty.ofBits, toWord, List.getD_cons_zero, List.getD_cons_succ,
      $[$lookup],*, ofProp_ne_zero, ite_true, ite_false, Bool.false_eq_true, Nat.zero_mod, hst,
      beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat, Int.reducePow] at hsi),
    ← `(tactic| all_goals simp only [wordMod, Nat.reducePow] at hsi),
    ← `(tactic| all_goals simp (disch := $disch:tactic) only [Nat.cast_ofNat,
      Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
      toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
      Nat.reduceDiv, Int.reducePow] at hsi)]

/-- `tree_succeeds [defs]` proves `TreeSucceeds b fs ctx n T` for a function of at most eight
parameters that reads no mapping: it decodes the argument words, evaluates the tree and the
succeeds-if terms, splits every branch and closes each by `omega`. -/
macro "tree_succeeds" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  seqTactics (#[← `(tactic| intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hsi),
    ← `(tactic| simp only [Nat.reducePow] at hs), ← chainTactics (← decodeArgs ds)] ++
    (← succeedsSteps ds false) ++
    #[← `(tactic| all_goals ((try split_ifs) <;> (try rfl) <;> first | omega | (simp_all; done) | (simp_all; omega)))])

/-- `tree_succeeds_map [defs] hsep`: `tree_succeeds` for a function that reads mappings keyed by
addresses at the slots `ms`, from `hsep : MapSlotsSeparated ms`, as `tree_meets_map` does. -/
macro "tree_succeeds_map" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => do
  seqTactics (#[← `(tactic| intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hsi),
    ← `(tactic| simp only [Nat.reducePow] at hs),
    ← chainTactics ((← decodeArgs ds) ++ (← hashLinks (← `(map_inj' $hsep)) (← `(map_ge' $hsep))))] ++
    (← succeedsSteps ds true) ++
    #[← `(tactic| all_goals ((try split_ifs) <;> (try rfl) <;> first
      | (hash_facts H s hinj hge hlt hs; omega)
      | (hash_facts H s hinj hge hlt hs; simp_all; done)
      | (hash_facts H s hinj hge hlt hs; simp_all; omega)))])

/-- `tree_meets_map' [defs] hsep`: `tree_meets_map`, with each simplification step allowed to make
no progress (a spec with no invariants, or a goal a step leaves alone), as `spec_connect` uses it for
a spec whose succeeds-if conditions `tree_succeeds_map` proves apart. -/
macro "tree_meets_map'" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => do
  seqTactics (#[← `(tactic| intro args s iargs pre hl hargs hs hdec hst ht hreq hinv),
    ← `(tactic| simp only [Nat.reducePow] at hs),
    ← chainTactics ((← decodeArgs ds) ++ (← hashLinks (← `(map_inj' $hsep)) (← `(map_ge' $hsep))) ++
      #[← `(tactic| refine ⟨fun hsucc => ?_, fun hne => ?_⟩)])] ++
    (← meetsSteps ds true false (← invBase)) ++
    #[← splitGoals false, ← `(tactic| all_goals (hash_facts H s hinj hge hlt hs; (try split_ifs) <;> first | omega | (simp_all; done) | (simp_all; omega)))])

end SolidCore.Spec

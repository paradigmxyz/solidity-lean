import Verify.VC.Model
import Verify.Spec.Contract

/-!
# A spec from the erased tree, for every function of the generic source stage

The generic source stage runs every call of a function of its fragment as the function's erased
tree (`Generic.source_run`). So a function's spec holds of SolidCore's checked contract on the
stage's calls as soon as it holds of the tree: `TreeMeets b fs ctx n T` says that from any `n`
argument words decoding to the spec's arguments, any storage of words and any pre-state on that
storage meeting the requires and the invariants, the tree's observable meets `Post` (for every
ghost state after the call, so a ghost-free spec). It speaks of the tree and the spec alone: no
SolidCore run, no ABI, no fuel. `holdsFn_of_tree` turns it into the spec's `HoldsFn` against
SolidCore on `stageScope`, which a refinement then carries to the bytecode
(`HoldsFn.of_stage`).

No solver verdict and no encoding of solar-verify's enters: the statement is solar-verify's exported
spec (`--emit-lean-spec`) read with `Spec.eval`, and the tree is the generic stage's.
-/

namespace SolidCore.Spec

open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

theorem bytesWord_map (l : List UInt8) :
    bytesWord (l.map (·.toNat)) = EthLib.Base.bytesToNat l := by
  simp [bytesWord, EthLib.Base.bytesToNat, List.foldl_map]

theorem bytesWord_natToBytes {v : Nat} (h : v < 2 ^ 256) :
    bytesWord ((EthLib.Base.natToBytes 32 v).map (·.toNat)) = v := by
  rw [bytesWord_map, EthLib.Base.bytesToNat_natToBytes_of_lt]
  simpa using h

/-- A 32-byte word in front: its word, then the words of the rest. -/
theorem words_append32 {x : List Nat} (hx : x.length = 32) (r : List Nat) :
    words (x ++ r) = bytesWord x :: words r := by
  unfold words
  rw [List.length_append, hx, show (32 + r.length) / 32 = r.length / 32 + 1 by omega,
    List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.mul_zero, List.drop_zero]
  refine congrArg₂ _ ?_ ?_
  · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    have hd : List.drop (32 + 32 * i) (x ++ r) = List.drop (32 * i) r := by
      rw [← List.drop_drop, List.drop_left' hx]
    rw [show 32 * (i + 1) = 32 + 32 * i by omega, hd]

theorem words_argBytes : ∀ (args : List Nat), (∀ a ∈ args, a < 2 ^ 256) →
    words (Dirty.argBytes args) = args
  | [], _ => by simp [Dirty.argBytes, words]
  | a :: as, h => by
    have ha := h a (List.mem_cons_self ..)
    have hs : Dirty.argBytes (a :: as) = (EthLib.Base.natToBytes 32 a).map (·.toNat) ++
        Dirty.argBytes as := by simp [Dirty.argBytes]
    rw [hs, words_append32 (by simp [EthLib.Base.natToBytes_length]), bytesWord_natToBytes ha,
      words_argBytes as fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The words after the selector of the stage's call data are the arguments. -/
theorem words_calldata (sel : Nat) {args : List Nat} (h : ∀ a ∈ args, a < 2 ^ 256) :
    words (((calldata sel args).data.toList.map (·.toNat)).drop 4) = args := by
  rw [Dirty.bytes_calldata, Wide.drop_selector, words_argBytes args h]

theorem foldl_bytesWord (a : Nat) (l : List Nat) :
    l.foldl (fun acc b => acc * 256 + b) a = a * 256 ^ l.length + bytesWord l := by
  induction l generalizing a with
  | nil => simp [bytesWord]
  | cons x l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, show bytesWord (x :: l) = List.foldl (fun acc b => acc * 256 + b) (0 * 256 + x) l from rfl,
      ih, Nat.pow_succ, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.add_assoc]
    ac_rfl

theorem bytesWord_cons (x : Nat) (l : List Nat) :
    bytesWord (x :: l) = x * 256 ^ l.length + bytesWord l := by
  show List.foldl (fun acc b => acc * 256 + b) (0 * 256 + x) l = _
  rw [foldl_bytesWord, Nat.zero_mul, Nat.zero_add]

/-- The big-endian bytes of `v`'s low `n` bytes, read back as a word. -/
theorem bytesWord_range_reverse (v : Nat) : ∀ n,
    bytesWord ((List.range n).reverse.map fun i => v / 256 ^ i % 256) = v % 256 ^ n
  | 0 => by rw [Nat.pow_zero, Nat.mod_one]; rfl
  | n + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, bytesWord_cons, bytesWord_range_reverse v n, List.length_map, List.length_reverse,
      List.length_range, Nat.mod_pow_succ]
    ac_rfl

/-- The 32 output bytes of a returned word (`wordOBytes e`, as the erased tree spells them out), read
back as words: the word, then the words of the rest. `tree_meets` rewrites with it before the bytes are
evaluated one by one, so a returned word that is not a literal (a storage word, an argument) reaches
the spec as one word. -/
theorem words_byteOf (ρ : Val) (e : WExpr) (rest : List OByte) :
    words (List.map (OByte.eval ρ) (.byteOf e 0 :: .byteOf e 1 :: .byteOf e 2 :: .byteOf e 3 :: .byteOf e 4 :: .byteOf e 5 :: .byteOf e 6 :: .byteOf e 7 ::
        .byteOf e 8 :: .byteOf e 9 :: .byteOf e 10 :: .byteOf e 11 :: .byteOf e 12 :: .byteOf e 13 :: .byteOf e 14 :: .byteOf e 15 ::
        .byteOf e 16 :: .byteOf e 17 :: .byteOf e 18 :: .byteOf e 19 :: .byteOf e 20 :: .byteOf e 21 :: .byteOf e 22 :: .byteOf e 23 ::
        .byteOf e 24 :: .byteOf e 25 :: .byteOf e 26 :: .byteOf e 27 :: .byteOf e 28 :: .byteOf e 29 :: .byteOf e 30 :: .byteOf e 31 :: rest)) =
      (e.eval ρ % 2 ^ 256) :: words (List.map (OByte.eval ρ) rest) := by
  have h : List.map (OByte.eval ρ) (.byteOf e 0 :: .byteOf e 1 :: .byteOf e 2 :: .byteOf e 3 :: .byteOf e 4 :: .byteOf e 5 :: .byteOf e 6 :: .byteOf e 7 ::
        .byteOf e 8 :: .byteOf e 9 :: .byteOf e 10 :: .byteOf e 11 :: .byteOf e 12 :: .byteOf e 13 :: .byteOf e 14 :: .byteOf e 15 ::
        .byteOf e 16 :: .byteOf e 17 :: .byteOf e 18 :: .byteOf e 19 :: .byteOf e 20 :: .byteOf e 21 :: .byteOf e 22 :: .byteOf e 23 ::
        .byteOf e 24 :: .byteOf e 25 :: .byteOf e 26 :: .byteOf e 27 :: .byteOf e 28 :: .byteOf e 29 :: .byteOf e 30 :: .byteOf e 31 :: rest) =
      ((List.range 32).reverse.map fun i => e.eval ρ / 256 ^ i % 256) ++
        List.map (OByte.eval ρ) rest := rfl
  rw [h, words_append32 (by simp), bytesWord_range_reverse]
  rfl

/-- What a function's spec asks of its erased tree: see the module comment. -/
def TreeMeets (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) : Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State) (ghost' : Ghost),
    args.length = n → (∀ a ∈ args, a < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    Post b fs ctx pre ghost' (T.eval ⟨args, s, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs iargs

/-- **A function's spec holds of SolidCore's contract when it holds of the erased tree**, on
the stage's calls of the function (any argument words, no value, any storage covering the
deployed one), for a call context fixed on those calls. -/
theorem holdsFn_of_tree {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hm : TreeMeets b fs ctx fn.params.length T) :
    HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs := by
  rintro _ ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ iargs pre hpre
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  have hrun := source_run hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hctx _ rfl] at ht hreq hinv ⊢
  rw [words_calldata _ hargs] at hdec
  exact ⟨_, hrun, hm args (slotValue σ) iargs pre _ hl hargs (fun k => Generic.slotValue_lt σ k)
    hdec hst ht hreq hinv⟩

/-! ## Functions that leave the ghost state alone -/

/-- `TreeMeets` for a function whose calls leave the ghost state as it was: the post-state's
ghost state is the pre-state's. -/
def TreeMeetsFixed (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) : Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ a ∈ args, a < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    Post b fs ctx pre pre.ghost (T.eval ⟨args, s, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs iargs

/-- **`holdsFn_of_tree` for a function that leaves the ghost state alone**: the ghost step is the
identity on the stage's calls of the function. -/
theorem holdsFn_of_tree_fixed {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fn s call → ∀ g, step call g = g)
    (hm : TreeMeetsFixed b fs ctx fn.params.length T) :
    HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs := by
  intro call hcall iargs pre hpre
  have hg := hstep call hcall pre.ghost
  obtain ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ := hcall
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  have hrun := source_run hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hctx _ rfl] at ht hreq hinv ⊢
  rw [words_calldata _ hargs] at hdec
  rw [hg]
  exact ⟨_, hrun, hm args (slotValue σ) iargs pre hl hargs (fun k => Generic.slotValue_lt σ k)
    hdec hst ht hreq hinv⟩

/-! ## Proving `TreeMeets`

`tree_meets [defs]` proves `TreeMeets b fs ctx n T` for a function of at most eight parameters
and no succeeds-if conditions, unfolding `defs` (the tree, the spec bundle and the function's
spec): it names the argument words, decodes them, splits the tree's branches, evaluates the spec's
terms and the tree's words (a returned word as one word, by `words_byteOf`, with storage words
bounded by `hsm` and `hsi`), and closes each case with `omega`. A goal it cannot close stays an
error: it never leaves a `sorry`. -/

macro "tree_meets" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro args s iargs pre g hl hargs hs hdec hst ht hreq hinv
  have hsm : ∀ k, s k % 2 ^ 256 = s k := fun k => Nat.mod_eq_of_lt (hs k)
  have hsi : ∀ k, ((s k : Nat) : Int) % 2 ^ 256 = s k := fun k =>
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have := hs k; omega)
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> (try omega) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true] at hargs <;>
    simp only [$ds,*, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords, Ty.ofWord,
      hargs, ite_true, bind, pure, Option.bind,
      Option.some.injEq] at hdec <;>
    subst hdec <;>
    refine ⟨fun hsucc => ?_, fun hne => ?_⟩ <;>
    first
    | (simp [$ds,*] at hne; done)
    | (simp only [$ds,*, Tree.eval, Res.obs, words_byteOf, WExpr.eval, BinOp.eval, Generic.wordSize, hsm,
          List.getD_cons_zero, List.getD_cons_succ] at hsucc ⊢
       split_ifs at hsucc ⊢ <;>
       simp_all [$ds,*, Res.obs, Writes.store, WExpr.eval, BinOp.eval, Bundle.satAll, Bundle.sat,
         eval, slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, Ty.ofWord, toWord, decodeWords, words,
         Generic.wordSize] <;>
       omega)))

/-- `tree_meets` for `TreeMeetsFixed`: the same steps, with the post-state's ghost state the
pre-state's. -/
macro "tree_meets_fixed" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv
  have hsm : ∀ k, s k % 2 ^ 256 = s k := fun k => Nat.mod_eq_of_lt (hs k)
  have hsi : ∀ k, ((s k : Nat) : Int) % 2 ^ 256 = s k := fun k =>
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have := hs k; omega)
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> (try omega) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true] at hargs <;>
    simp only [$ds,*, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords, Ty.ofWord,
      hargs, ite_true, bind, pure, Option.bind,
      Option.some.injEq] at hdec <;>
    subst hdec <;>
    refine ⟨fun hsucc => ?_, fun hne => ?_⟩ <;>
    first
    | (simp [$ds,*] at hne; done)
    | (simp only [$ds,*, Tree.eval, Res.obs, words_byteOf, WExpr.eval, BinOp.eval, Generic.wordSize, hsm,
          List.getD_cons_zero, List.getD_cons_succ] at hsucc ⊢
       split_ifs at hsucc ⊢ <;>
       simp_all [$ds,*, Res.obs, Writes.store, WExpr.eval, BinOp.eval, Bundle.satAll, Bundle.sat,
         eval, slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, Ty.ofWord, toWord, decodeWords, words,
         Generic.wordSize] <;>
       omega)))

end SolidCore.Spec

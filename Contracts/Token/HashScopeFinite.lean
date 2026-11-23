import Verify.Spec.HashScopeFinite
import Contracts.Token.HashScope
import Contracts.Token.SpecTree

/-!
# Token's `transfer` under keccak256 separation on a finite set of accounts

Contracts/Token/HashScope.lean states `transfer`'s per-call premise `TransferFP args`: keccak256
separated on the two `balanceOf` preimages (slot 0) of the caller `0x2000` and the recipient
`args.getD 0 0 % 2 ^ 160`. Verify/Spec/HashScopeFinite.lean states `KeccakSep S`, the same premise on
a finite set `S` of preimages. This file takes `S = balancePreimages 0 A` for a finite set `A` of
addresses with `0x2000 ∈ A`:

* `transferFP_of_keccakSep`: `TransferFP args` for every `args` whose recipient is in `A`.
* `collide_not_meets_at`: the collision spec of scripts/verify/keccak/TokenSpecCollide.sol is refuted
  on `transfer(t, 0)` for every address `t ≠ 0x2000` whose call premise holds (`collide_not_meets_scoped`
  is the case `t = 1`); `collide_not_meets_finite` is every `t ∈ A` other than `0x2000`, under
  `KeccakSep (balancePreimages 0 A)`.
* `transfer_meets_fp`, `transfer_meets_finite`, `transfer_holds_finite`: the exported spec of
  `transfer` **without its frame clause** (`localSpec`: the caller's debit, the recipient's credit,
  the unchanged `totalSupply` and the invariant), of the erased tree on every call whose premise
  holds, then on every call whose recipient is in `A`, then of SolidCore's checked Token
  (`HoldsFnUnder`).
* `transfer_store_frame`, `transfer_frame_finite`: the frame the finite premise does give. A call
  writes only the caller's and the recipient's balance slots (no premise), so the balance of every
  other address of `A` is unchanged.
* `real_addrs3`: the premise for `A = {0x2000, 1, 2}` at the real keccak256, by one kernel
  evaluation; the results above then hold for those three addresses with no hypothesis left.

**What the finite premise does not give.** `transfer_meets` (TransferMeets.lean) proves the full
exported spec from `SlotsSeparated 0`: keccak256 injective, with images at least `2 ^ 128`, on
the `balanceOf` preimages of all `2 ^ 160` addresses, the global premise
(`universalTransferSep_iff`: it is `UniversalTransferSep 0`). Counting does not refute it
(`2 ^ 160` preimages into `2 ^ 256` words) but it is a claim about all `2 ^ 160` hashes at once.
The exported frame clause, `∀ a, a ≠ msg.sender ∧ a ≠ to → balanceOf[a] == old(balanceOf[a])`,
quantifies over every address, so it needs `solHash a 0` apart from the two written slots for
every `a < 2 ^ 160`, which no premise on a finite set of preimages gives. `localSpec` is the
exported spec with exactly that clause removed (`transferSpec_ensures_eq`), and the frame is
stated over `A` instead.
-/

namespace SolidCore.Spec.TreeDemo.Token

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Verify.VC.Token
open TrustedBase

/-! ## The call premise from the finite one -/

/-- **`transfer`'s premise for every recipient in `A`**: from keccak256 separation on the
`balanceOf` preimages of `A`, with the caller `0x2000` in `A`. -/
theorem transferFP_of_keccakSep {A : Finset Nat} (h : KeccakSep (balancePreimages 0 A))
    (hc : 0x2000 ∈ A) {args : List Nat} (ht : args.getD 0 0 % 2 ^ 160 ∈ A) : TransferFP args :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [transferFootprint, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_image_of_mem (fun k => mappingPreimage k 0) hc
    · exact Finset.mem_image_of_mem (fun k => mappingPreimage k 0) ht

/-- A tree spec on the calls meeting `P` holds on the calls meeting any stronger `Q`. -/
theorem treeMeetsFixedOn_weaken {P Q : Val → Prop} {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat}
    {T : Tree} (h : TreeMeetsFixedOn P b fs ctx n T) (hQP : ∀ ρ, Q ρ → P ρ) :
    TreeMeetsFixedOn Q b fs ctx n T :=
  fun args s iargs pre hl hargs hs hdec hst ht hreq hinv hq =>
    h args s iargs pre hl hargs hs hdec hst ht hreq hinv (hQP _ hq)

/-! ## The collision spec, refuted for every recipient -/

set_option linter.unusedSimpArgs false in
/-- **The collision spec is refuted on `transfer(t, 0)` for every address `t ≠ 0x2000`** whose call
premise holds, on any set of calls `P` that contains that call (at every storage): from the storage
where the caller holds 5 and every other slot 0, the call succeeds with `balanceOf[t]` still 0, and
the collision spec asks for 5. -/
theorem collide_not_meets_at {P : Val → Prop} {t : Nat} (hto : t < 2 ^ 160) (hne : t ≠ 0x2000)
    (hfp : TransferFP [t, 0]) (hP : ∀ s, P ⟨[t, 0], s, solHash, callerWord⟩) :
    ¬ TreeMeetsFixedOn P SolidCore.Spec.Export.TokenSpecCollide.Token collideSpec ctx 2
      transferTree := by
  intro h
  have hl160 : t < 1461501637330902918203684832716283019655932542976 := by simpa using hto
  have hl256 : t < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    omega
  have hP' : ScopedSep (transferFootprint 0 8192 t) := by
    simpa [TransferFP, Nat.mod_eq_of_lt hl160] using hfp
  obtain ⟨hne', hge0, hge1⟩ := transfer_slots hP' (by decide) (by decide) (by omega)
  have hne2 : solHash t 0 ≠ solHash 8192 0 := fun he => hne' (fun h => hne h.symm) he.symm
  have hs : ∀ k, collideStore k < 2 ^ 256 := fun k => by unfold collideStore; split <;> omega
  have h1 : (1 : Nat) ≠ solHash 8192 0 := by omega
  have hto' : t < 2 ^ 256 := by omega
  have hp := h [t, 0] collideStore [(t : Int), 0] ⟨collideStore, Ghost.zero, 0⟩ rfl
    (by simp [hl256]) hs
    (by simp [collideSpec, SolidCore.Spec.Export.TokenSpecCollide.Token, decodeWords, Ty.ofWord, hl160])
    rfl (by simp [ctx])
    (by simp [Bundle.satAll, collideSpec, SolidCore.Spec.Export.TokenSpecCollide.Token])
    (by simp [Bundle.satAll, Bundle.sat, SolidCore.Spec.Export.TokenSpecCollide.Token, eval, slotOf, mkEnv,
      Env.cur, Ghost.zero, BinOp.apply, Ty.ofBits, collideStore, h1])
    (hP _)
  have hlt := solHash_lt'
  have hkec := keccak_solHash
  have htm : t % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = t :=
    Nat.mod_eq_of_lt hl256
  have hgt : ¬ 1461501637330902918203684832716283019655932542975 < t := by omega
  unfold collideStore at hp
  generalize solHash = H at hp hlt hkec hge0 hge1 hne2
  have hm1 := Nat.mod_eq_of_lt (hlt t 0)
  have hm2 := Nat.mod_eq_of_lt (hlt 8192 0)
  simp only [transferTree, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow, Nat.reduceMod, Nat.zero_mod,
    Nat.reduceLT, ite_mod_nat, ite_true, ite_false, Nat.lt_irrefl, Nat.not_lt_zero, decide_false,
    Nat.reduceAdd, Nat.reduceSub, Nat.zero_add, Nat.add_zero, ite_self, Nat.one_ne_zero, ite_false,
    Nat.reduceEqDiff, reduceIte, hne2, htm, hm1, hm2, hgt] at hp
  obtain ⟨rets, -, hens, -⟩ := hp.1 (by simp_all)
  clear hp
  simp only [Bundle.satAll, Bundle.sat, collideSpec, SolidCore.Spec.Export.TokenSpecCollide.Token,
    List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv, Env.cur, Env.bind, BinOp.apply, Ty.ofBits,
    toWord, ctx, List.getD_cons_zero, List.getD_cons_succ, hkec, ofProp_ne_zero, ite_true, ite_false,
    Nat.zero_div, Nat.zero_mod, Int.reduceMod, Int.reduceToNat] at hens
  have k2 := hens.2.1 (by omega)
  clear hens
  simp only [wordMod, Nat.reducePow, Int.reducePow, Nat.cast_ofNat, Int.reduceMod, Int.reduceToNat, Nat.reduceMul, Nat.pow_zero, Nat.div_one, Nat.reduceMod, Nat.mul_zero, Int.toNat_zero, Int.zero_emod, hm2, hm1] at k2
  generalize hx : ((t : Int) % 115792089237316195423570985008687907853269984665640564039457584007913129639936).toNat = x at k2
  have hxt : x = t := by omega
  subst hxt
  simp only [Bool.false_eq_true, ite_false, ite_true, hm1, hm2, Nat.cast_ofNat, Nat.reduceMod] at k2
  omega

/-- `collide_not_meets_scoped` is its case `t = 1`. -/
theorem collide_not_meets_scoped' (hP : TransferFP [1, 0]) :
    ¬ TreeMeetsFixedOn (fun ρ => TransferFP ρ.args) SolidCore.Spec.Export.TokenSpecCollide.Token
      collideSpec ctx 2 transferTree :=
  collide_not_meets_at (by decide) (by decide) hP fun _ => hP

/-- **Under the finite premise, the collision spec is refuted at every recipient `t ∈ A` other than
the caller**, both on the calls whose recipient is in `A` and on the calls whose own premise holds. -/
theorem collide_not_meets_finite {A : Finset Nat} (h : KeccakSep (balancePreimages 0 A))
    (hc : 0x2000 ∈ A) (hA : ∀ x ∈ A, x < 2 ^ 160) {t : Nat} (ht : t ∈ A) (hne : t ≠ 0x2000) :
    ¬ TreeMeetsFixedOn (fun ρ => ρ.args.getD 0 0 % 2 ^ 160 ∈ A)
        SolidCore.Spec.Export.TokenSpecCollide.Token collideSpec ctx 2 transferTree ∧
      ¬ TreeMeetsFixedOn (fun ρ => TransferFP ρ.args) SolidCore.Spec.Export.TokenSpecCollide.Token
        collideSpec ctx 2 transferTree := by
  have hm : [t, 0].getD 0 0 % 2 ^ 160 ∈ A := by
    simpa only [List.getD_cons_zero, Nat.mod_eq_of_lt (hA t ht)] using ht
  have hfp : TransferFP [t, 0] := transferFP_of_keccakSep h hc hm
  exact ⟨collide_not_meets_at (hA t ht) hne hfp fun _ => hm,
    collide_not_meets_at (hA t ht) hne hfp fun _ => hfp⟩

/-! ## The exported spec without its frame clause -/

/-- The exported spec of `transfer` with its frame clause (`ensures[2]`, over every other address)
removed: the caller's debit, the recipient's credit and the unchanged `totalSupply`, with the
same parameters, returns, requires and invariant. -/
def localSpec : FnSpec := { transferSpec with ensures := transferSpec.ensures.eraseIdx 2 }

/-- The exported spec is `localSpec` with the frame clause put back at position 2. -/
theorem transferSpec_ensures_eq :
    transferSpec.ensures =
      localSpec.ensures.take 2 ++ transferSpec.ensures[2]'(by decide) :: localSpec.ensures.drop 2 :=
  rfl

/-- The call premise at `transfer`'s two keys, in `scope_inj`'s shape. -/
theorem fp_inj {c t : Nat} (h : ScopedSep (transferFootprint 0 c t)) (m n : Nat) (hm : m ∈ [0])
    (hn : n ∈ [0]) (hmw : m < 2 ^ 256) (hnw : n < 2 ^ 256) (a b : Nat)
    (hK : (a = c ∨ a = t) ∧ (b = c ∨ b = t)) :
    a < 2 ^ 160 → b < 2 ^ 160 → solHash a m = solHash b n → a = b ∧ m = n := by
  intro ha hb he
  simp only [List.mem_singleton] at hm hn
  subst hm hn
  have hx : ∀ k, (k = c ∨ k = t) → mappingPreimage k 0 ∈ transferFootprint 0 c t := by
    rintro k (rfl | rfl) <;> simp [transferFootprint]
  exact scoped_inj h (by omega) (by omega) hmw hnw (hx a hK.1) (hx b hK.2) he

/-- The call premise at `transfer`'s two keys, in `scope_ge`'s shape. -/
theorem fp_ge {c t : Nat} (h : ScopedSep (transferFootprint 0 c t)) (m : Nat) (hm : m ∈ [0])
    (a : Nat) (hK : a = c ∨ a = t) : 2 ^ 128 ≤ solHash a m := by
  simp only [List.mem_singleton] at hm
  subst hm
  rcases hK with rfl | rfl <;> exact scoped_ge h (by simp [transferFootprint])

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **The exported spec of `transfer` without its frame clause, under the call's own premise**: on
every call whose footprint premise `TransferFP` holds, the caller's debit, the recipient's credit,
the unchanged `totalSupply` and the invariant `totalSupply == sumBalances`. The instances of the
premise come from `fp_inj` and `fp_ge` at the two keys of the call, as `tree_meets_scoped` does for
`MapScope`. -/
theorem transfer_meets_fp :
    TreeMeetsFixedOn (fun ρ => TransferFP ρ.args) spec localSpec ctx 2 transferTree := by
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hP
  simp only [Nat.reducePow] at hs
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> (try omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    IsEmpty.forall_iff, implies_true, and_true, Nat.reducePow] at hargs
  simp only [transferTree, localSpec, transferSpec, SolidCore.Spec.TreeDemo.Token.spec, SolidCore.Spec.Export.Token.Token, SolidCore.Spec.TreeDemo.Token.ctx, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords, Ty.ofWord,
    bind, pure, Option.bind, Nat.reducePow] at hdec
  split_ifs at hdec
  simp only [Option.some.injEq, reduceCtorEq] at hdec
  subst hdec
  simp only [TransferFP, List.getD_cons_zero, Nat.reducePow] at hP
  simp (disch := omega) only [Nat.mod_eq_of_lt] at hP
  have hinj := fp_inj hP
  have hge := fp_ge hP
  have hlt := solHash_lt'
  have hkec := keccak_solHash
  have ha0 : a0 < 2 ^ 160 := by omega
  generalize solHash = H at hinj hge hlt hkec ⊢
  have i1 : H a0 0 = H 8192 0 → a0 = 8192 := fun he =>
    (hinj 0 0 (by simp) (by simp) (by decide) (by decide) a0 8192 (by simp) ha0 (by decide) he).1
  have g1 : 2 ^ 128 ≤ H a0 0 := hge 0 (by simp) a0 (by simp)
  have g2 : 2 ^ 128 ≤ H 8192 0 := hge 0 (by simp) 8192 (by simp)
  simp only [Nat.reducePow] at g1 g2
  refine ⟨fun hsucc => ?_, fun hne => ?_⟩
  all_goals try (simp [transferTree, localSpec, transferSpec, SolidCore.Spec.TreeDemo.Token.spec, SolidCore.Spec.Export.Token.Token, SolidCore.Spec.TreeDemo.Token.ctx, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero] at hne; done)
  all_goals simp only [transferTree, localSpec, transferSpec, SolidCore.Spec.TreeDemo.Token.spec, SolidCore.Spec.Export.Token.Token, SolidCore.Spec.TreeDemo.Token.ctx, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow] at hsucc ⊢
  all_goals simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not] at hsucc ⊢
  all_goals split_ifs at hsucc ⊢
  all_goals simp only [Bool.false_eq_true, Bool.true_eq_false, imp_false, not_true_eq_false,
    IsEmpty.forall_iff] at hsucc
  all_goals simp only [transferTree, localSpec, transferSpec, SolidCore.Spec.TreeDemo.Token.spec, SolidCore.Spec.Export.Token.Token, SolidCore.Spec.TreeDemo.Token.ctx, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, OByte.eval, WExpr.eval, Generic.wordSize, words, bytesWord, decodeWords, Ty.ofWord,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.drop_zero, List.take_succ_cons, List.take_zero, List.foldl_cons,
    List.foldl_nil, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceLT, ite_true, ite_false, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq,
    exists_eq_left', bind, pure, Option.bind, Ty.InRange, Nat.cast_ofNat, Nat.zero_add,
    Nat.reduceLeDiff] at hsucc ⊢
  all_goals try clear hsucc
  all_goals try refine ⟨?_, ?_⟩
  all_goals simp only [Bundle.satAll, Bundle.sat, transferTree, localSpec, transferSpec, SolidCore.Spec.TreeDemo.Token.spec, SolidCore.Spec.Export.Token.Token, SolidCore.Spec.TreeDemo.Token.ctx, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, List.getElem_cons_succ, List.getElem_cons_zero,
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
  all_goals (hash_facts_scoped H s hinj hge hlt hs; split_ifs <;> omega)

/-- **`localSpec` on every call whose recipient is in `A`**, under keccak256 separation on the
`balanceOf` preimages of `A` (`0x2000 ∈ A`). -/
theorem transfer_meets_finite {A : Finset Nat} (h : KeccakSep (balancePreimages 0 A))
    (hc : 0x2000 ∈ A) :
    TreeMeetsFixedOn (fun ρ => ρ.args.getD 0 0 % 2 ^ 160 ∈ A) spec localSpec ctx 2 transferTree :=
  treeMeetsFixedOn_weaken transfer_meets_fp fun _ hρ => transferFP_of_keccakSep h hc hρ

/-- **`localSpec` of SolidCore's checked Token on the stage's calls of `transfer` whose recipient
word is in `A`**, under the finite premise (`holdsFnUnder_of_tree_fixed`). -/
theorem transfer_holds_finite {A : Finset Nat} (h : KeccakSep (balancePreimages 0 A))
    (hc : 0x2000 ∈ A) {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hcon : contract? = .ok c)
    (step : GhostStep)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fnTransfer [(2, 4096)] call → ∀ g, step call g = g) :
    HoldsFnUnder (fun call => (callArgs call).getD 0 0 % 2 ^ 160 ∈ A) (solidCore fuel) c
      (SolidCore.Verify.VC.stageScope fnTransfer [(2, 4096)]) spec ctxOf step localSpec := by
  have hdep := burnShape_eq
  simp only [burnShape?, hcon, Option.some.injEq, Prod.mk.injEq] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep.1
  have hshape := transferShape_eq
  simp only [transferShape?, hcon, Option.some.injEq, Option.map_eq_some_iff, Prod.mk.injEq] at hshape
  obtain ⟨f, hf, hlen, hT⟩ := hshape
  exact holdsFnUnder_of_tree_fixed (fn := fnTransfer) (P := fun args => args.getD 0 0 % 2 ^ 160 ∈ A)
    hd (by decide) hf hlen hT (fun call h => by simp [ctxOf, ctx, h]) hstep (transfer_meets_finite h hc)

/-! ## The frame over `A` -/

set_option linter.unusedSimpArgs false in
/-- **`transfer` writes only the caller's and the recipient's balance slots**, with no premise:
every other slot holds what it held. -/
theorem transfer_store_frame {t v : Nat} (ht : t < 2 ^ 256) (hv : v < 2 ^ 256) {s : Storage}
    {k : Nat} (hk : k < 2 ^ 256) (h1 : k ≠ solHash 8192 0)
    (h2 : k ≠ solHash t 0) :
    (transferTree.eval ⟨[t, v], s, solHash, callerWord⟩).store k = s k := by
  have hlt := solHash_lt'
  generalize solHash = H at hlt h1 h2 ⊢
  simp only [Nat.reducePow] at ht hv hk
  have hm1 := Nat.mod_eq_of_lt (hlt t 0)
  have hm2 := Nat.mod_eq_of_lt (hlt 8192 0)
  have hmk := Nat.mod_eq_of_lt hk
  have hmt := Nat.mod_eq_of_lt ht
  have hmv := Nat.mod_eq_of_lt hv
  simp only [transferTree, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow, Nat.reduceMod, hm1, hm2, hmk,
    hmt, hmv]
  split_ifs <;> simp only [hmk] <;> (try split_ifs) <;> omega

/-- **The balance of every other address of `A` is unchanged** by `transfer(t, v)` for `t ∈ A`,
under the finite premise. -/
theorem transfer_frame_finite {A : Finset Nat} (h : KeccakSep (balancePreimages 0 A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (hc : 0x2000 ∈ A) {t v : Nat} (ht : t ∈ A) (hv : v < 2 ^ 256)
    {s : Storage} {a : Nat} (ha : a ∈ A) (hac : a ≠ 0x2000) (hat : a ≠ t) :
    (transferTree.eval ⟨[t, v], s, solHash, callerWord⟩).store (solHash a 0) = s (solHash a 0) := by
  have hL : ScopedSep [mappingPreimage a 0, mappingPreimage 8192 0, mappingPreimage t 0] :=
    scopedSep_of_keccakSep h fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_image_of_mem (fun k => mappingPreimage k 0) ha
      · exact Finset.mem_image_of_mem (fun k => mappingPreimage k 0) hc
      · exact Finset.mem_image_of_mem (fun k => mappingPreimage k 0) ht
  have hal := hA a ha
  have htl := hA t ht
  refine transfer_store_frame (by omega) hv (solHash_lt a 0) (fun he => hac ?_) (fun he => hat ?_)
  · exact (scoped_inj hL (by omega) (by decide) (by decide) (by decide) (by simp) (by simp) he).1
  · exact (scoped_inj hL (by omega) (by omega) (by decide) (by decide) (by simp) (by simp) he).1

/-! ## A real witness: three addresses at keccak256 -/

/-- The caller and two other addresses. -/
def addrs3 : Finset Nat := {0x2000, 1, 2}

/-- The `balanceOf` preimages of `addrs3`, as a list. -/
def balList3 : List (List Nat) := [mappingPreimage 0x2000 0, mappingPreimage 1 0, mappingPreimage 2 0]

theorem balancePreimages_addrs3_sub : balancePreimages 0 addrs3 ⊆ balList3.toFinset := by
  intro x hx
  simp only [balancePreimages, addrs3, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hx
  rw [List.mem_toFinset]
  obtain ⟨k, hk, rfl⟩ := hx
  rcases hk with rfl | rfl | rfl <;> simp [balList3]

set_option maxRecDepth 100000 in
/-- The check at the real keccak256 on the three preimages: one kernel evaluation. -/
theorem real_balList3 : ScopedSep balList3 :=
  scopedSep_of_check (by decide +kernel)

/-- **The finite premise holds for `{0x2000, 1, 2}` at the real keccak256.** -/
theorem real_addrs3 : KeccakSep (balancePreimages 0 addrs3) :=
  ((keccakSep_toFinset_iff _).2 real_balList3).mono balancePreimages_addrs3_sub

theorem addrs3_lt : ∀ x ∈ addrs3, x < 2 ^ 160 := by decide

/-- `localSpec` on every call to one of the three addresses, with no hypothesis. -/
theorem real_transfer_meets_addrs3 :
    TreeMeetsFixedOn (fun ρ => ρ.args.getD 0 0 % 2 ^ 160 ∈ addrs3) spec localSpec ctx 2 transferTree :=
  transfer_meets_finite real_addrs3 (by decide)

/-- The collision spec, refuted at the recipient 2 (and at 1) with no hypothesis. -/
theorem real_collide_refuted_addrs3 :
    ¬ TreeMeetsFixedOn (fun ρ => ρ.args.getD 0 0 % 2 ^ 160 ∈ addrs3)
      SolidCore.Spec.Export.TokenSpecCollide.Token collideSpec ctx 2 transferTree :=
  (collide_not_meets_finite real_addrs3 (by decide) addrs3_lt (t := 2) (by decide) (by decide)).1

/-! ## Negative controls -/

set_option linter.unreachableTactic false in
/-- **A recipient outside `A` is refused**: from the real premise of `addrs3`, the call premise of
`transfer(2, 0)` elaborates and that of `transfer(3, 0)` does not (its side condition `3 ∈ addrs3`
is false), and neither does the refutation of the collision spec at 3. -/
theorem outside_recipient_rejected : True := by
  have _h2 : TransferFP [2, 0] := transferFP_of_keccakSep real_addrs3 (by decide) (by decide)
  fail_if_success
    have _h3 : TransferFP [3, 0] := transferFP_of_keccakSep real_addrs3 (by decide) (by decide)
  fail_if_success
    have _c3 := collide_not_meets_finite real_addrs3 (by decide) addrs3_lt (t := 3) (by decide)
      (by decide)
  fail_if_success
    have _cc := collide_not_meets_finite real_addrs3 (by decide) addrs3_lt (t := 0x2000) (by decide)
      (by decide)
  trivial

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.TreeDemo.Token.transferFP_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transferFP_of_keccakSep

/-- info: 'SolidCore.Spec.TreeDemo.Token.treeMeetsFixedOn_weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeMeetsFixedOn_weaken

/-- info: 'SolidCore.Spec.TreeDemo.Token.collide_not_meets_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collide_not_meets_at

/-- info: 'SolidCore.Spec.TreeDemo.Token.collide_not_meets_scoped'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collide_not_meets_scoped'

/-- info: 'SolidCore.Spec.TreeDemo.Token.collide_not_meets_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collide_not_meets_finite

/-- info: 'SolidCore.Spec.TreeDemo.Token.transferSpec_ensures_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms transferSpec_ensures_eq

/-- info: 'SolidCore.Spec.TreeDemo.Token.fp_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fp_inj

/-- info: 'SolidCore.Spec.TreeDemo.Token.fp_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fp_ge

/-- info: 'SolidCore.Spec.TreeDemo.Token.transfer_meets_fp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_meets_fp

/-- info: 'SolidCore.Spec.TreeDemo.Token.transfer_meets_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_meets_finite

/-- info: 'SolidCore.Spec.TreeDemo.Token.transfer_holds_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_holds_finite

/-- info: 'SolidCore.Spec.TreeDemo.Token.transfer_store_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_store_frame

/-- info: 'SolidCore.Spec.TreeDemo.Token.transfer_frame_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_frame_finite

/-- info: 'SolidCore.Spec.TreeDemo.Token.real_balList3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_balList3

/-- info: 'SolidCore.Spec.TreeDemo.Token.real_addrs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_addrs3

/-- info: 'SolidCore.Spec.TreeDemo.Token.real_transfer_meets_addrs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_transfer_meets_addrs3

/-- info: 'SolidCore.Spec.TreeDemo.Token.real_collide_refuted_addrs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_collide_refuted_addrs3

/-- info: 'SolidCore.Spec.TreeDemo.Token.outside_recipient_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outside_recipient_rejected

end SolidCore.Spec.TreeDemo.Token

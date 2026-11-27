import Verify.LoopSource.MirLink.Statement
import Verify.LoopSource.Generic.Link

/-!
# Counter.bump's Statement, as an instance of the generic link

`statement_link : StatementLink` is `generic_link` (`Generic/Link.lean`) at Counter's checked
contract, bump's selector, `bumpFn`, widths `[2 ^ 256 - 1]` and tree `bumpBr`, with the headline
`CounterBumpLoopHeadline` as the body's `BodyRuns`. The headline is a hypothesis here, never a
proof of it. The only Counter facts used are the kernel's check that the type checker's `bump` is
`bumpFn` (`Source.shape_of`) and that Counter's valid calls are the generic ones (`bump_valid`).
`tree_post` checks bump's postcondition on its loop-free tree.
-/

namespace Verify.LoopSource.MirLink
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source
open Verify.LoopSource.RC.Headline Verify.LoopSource.Generic

theorem args_one {a : Nat} (ha : a < 2 ^ 256) : ArgsOk bumpFn [2 ^ 256 - 1] [a] := by
  refine ⟨rfl, by simpa using ha, ?_⟩
  show (decide (a ≤ 2 ^ 256 - 1) && true) = true
  simp only [Bool.and_true, decide_eq_true_eq]
  exact Nat.le_of_lt_succ ha

theorem args_of_ok {args : List Nat} (h : ArgsOk bumpFn [2 ^ 256 - 1] args) :
    ∃ a, a < 2 ^ 256 ∧ args = [a] := by
  obtain ⟨hlen, hargs, -⟩ := h
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨a, hargs a (List.mem_singleton_self a), rfl⟩

/-- **Counter's valid calls are the generic ones** at bump's selector, function and widths. -/
theorem bump_valid : SelCall bumpSel bumpFn [2 ^ 256 - 1] = BumpCall := by
  funext call
  apply propext
  constructor
  · rintro ⟨σ, args, ha, rfl⟩
    obtain ⟨a, haw, rfl⟩ := args_of_ok ha
    exact ⟨σ, a, haw, rfl⟩
  · rintro ⟨σ, a, ha, rfl⟩
    exact ⟨σ, [a], args_one ha, rfl⟩

theorem onTree_of {Q : Call → Observable → Prop} (h : OnTree Q) {T : Tree}
    (hT : brTree bumpFn (argFacts [2 ^ 256 - 1] 0) bumpBr = some T) :
    Generic.OnTree bumpSel bumpFn [2 ^ 256 - 1] T Q := by
  intro σ args ha
  obtain ⟨a, haw, rfl⟩ := args_of_ok ha
  exact h T hT σ a haw

theorem bodyRuns_of_headline (hL : CounterBumpLoopHeadline)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    BodyRuns { envOf c.core with facts := argFacts [2 ^ 256 - 1] 0 } Contracts.VerifyCounter.Source.fuel
      bumpFn bumpBr := by
  rw [envOf_eq (shape_of hc).1]
  exact hL _ _ bumpFn rfl rfl _ (by unfold Contracts.VerifyCounter.Source.fuel; omega)

/-- **Counter's whole Statement from the headline**, by the generic link. -/
theorem statement_link : StatementLink := by
  intro hL code Allowed Post G hA hP heq hres
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨T, hT⟩ := tree_ok
  have h := generic_link Contracts.VerifyCounter.Source.fuel c bumpSel bumpFn [2 ^ 256 - 1] bumpBr T
    (by decide) (shape_of hc).2.2 rfl rfl (bodyRuns_of_headline hL hc) hT code Allowed Post G
    (onTree_of hA hT) (onTree_of hP hT) (by rw [bump_valid]; exact heq c hc)
    (by rw [bump_valid]; exact hres c hc)
  rw [bump_valid] at h
  exact ⟨c, hc, h⟩

/-- **bump's postcondition holds of its tree's observable**: read off the tree's guards. -/
theorem tree_post : OnTree BumpPost := by
  intro T hT σ a ha
  refine ⟨σ, a, ha, rfl, fun hs => ?_⟩
  set ρ : Val := ⟨[a], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩ with hρ
  have hok : ρ.Ok := slotValue_store σ
  obtain ⟨T', hT', hTe⟩ := brTree_eval bumpFn (argFacts [2 ^ 256 - 1] 0) ρ bumpBr T hT
  simp only [Res.obs] at hs ⊢
  rw [← hTe] at hs ⊢
  unfold bumpBr at hT'
  rw [guards_eval] at hT'
  by_cases hg : [ovf].any (fun g => g.eval ρ != 0) = true
  · rw [if_pos hg] at hT'
    simp only [leafTree, Option.some.injEq] at hT'
    subst hT'
    simp [Tree.eval] at hs
  rw [if_neg hg] at hT'
  simp only [Br.eval] at hT'
  by_cases hv : le.eval ρ = 0
  · rw [if_pos hv] at hT'
    simp only [leafTree, Option.map_eq_some_iff] at hT'
    obtain ⟨bs, _, rfl⟩ := hT'
    simp [Tree.eval] at hs
  rw [if_neg hv] at hT'
  have hpre := require_passed ρ hok hg hv
  have hn : nOf ρ = a := by
    simp only [nOf, WExpr.eval, hρ, List.getD_cons_zero]; exact Nat.mod_eq_of_lt ha
  rw [hn] at hpre
  have h1w := hok.word 1
  have h0 := hok.word 0
  have hT2 : T' = .halt true [] [(.lit 0, .bin .add (.init 0) (.arg 0))] [] := by
    simp [leafTree, bumpFn, SF, retsOk] at hT'
    first | exact hT'.symm | exact hT'
  subst hT2
  have h0' : slotValue σ 0 < Generic.wordSize := h0
  have h1' : slotValue σ 1 < Generic.wordSize := h1w
  have ha' : a < Generic.wordSize := ha
  have hpre' : slotValue σ 0 + a ≤ slotValue σ 1 := hpre
  refine ⟨?_, hpre', ?_⟩
  · simp only [Tree.eval, ↓reduceIte, Writes.store, WExpr.eval, BinOp.eval, hρ, List.getD_cons_zero]
    rw [Nat.mod_eq_of_lt h0', Nat.mod_eq_of_lt ha', Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  · intro k hk
    simp only [Tree.eval, ↓reduceIte, Writes.store, WExpr.eval]
    by_cases he : 0 % Generic.wordSize = k % Generic.wordSize
    · rw [Nat.zero_mod] at he; exact absurd he.symm hk
    · simp only [he, ↓reduceIte] <;> rfl

/-- **The Statement's source half from the headline**, by the generic run. -/
theorem source_half_of_headline (hL : CounterBumpLoopHeadline) : StatementSourceHalf := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨T, hT⟩ := tree_ok
  have hrun : ∀ σ a, a < 2 ^ 256 → stmtSem.run c (bumpCall σ a) =
      some (T.eval ⟨[a], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs :=
    fun σ a ha => runs_of_bodyRuns (by decide) (shape_of hc).2.2 rfl rfl
      (bodyRuns_of_headline hL hc) hT σ (args_one ha)
  refine ⟨c, hc, ?_, ?_⟩
  · rintro _ ⟨σ, a, ha, rfl⟩
    exact ⟨_, hrun σ a ha, trivial⟩
  · rintro _ ⟨σ, a, ha, rfl⟩ obs hs
    change stmtSem.run c (bumpCall σ a) = some obs at hs
    rw [hrun σ a ha] at hs
    obtain rfl := Option.some.inj hs
    exact tree_post T hT σ a ha

end Verify.LoopSource.MirLink

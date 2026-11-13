import Contracts.Token.VC.Transfer

/-!
# Token.transfer's obligations, discharged in Lean

`transfer_triple` takes solar-verify's verdict `Valid Export.Token.script` and reads each of
`transfer`'s three clauses off the obligation the checked script gives (`checkScript_sound`). The three
obligations `trObs` it uses hold in the array theory on their own: `trObs_valid` proves them for
every assignment, by the semantics of `select` and `store` (no solver, no verdict). So
`transfer_triple_discharged` is `transfer_triple` with the verdict gone: its one hypothesis is `HashInj`,
injectivity of the mapping slot on address keys. `transfer_check` (the kernel's check that solar-verify's
script has these obligations) still ties them to solar-verify's encoding of the clauses.
-/

namespace SolidCore.Verify.VC.Token

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic

/-- `transfer`'s three obligations hold at every assignment of the array theory. -/
theorem trObs_valid : ObsValid trObs := by
  intro o ho σ _
  simp only [trObs, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · simp only [trGoalFrom]
    simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.S2, Ob.S1, Ob.sto, Ob.ms, Ob.rcpt, Ob.B, Ob.bal, Ob.amt]
    intro h1 h2
    exact absurd h2 h1
  · simp only [trGoalTo]
    simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.S2, Ob.S1, Ob.sto, Ob.ms, Ob.rcpt, Ob.B, Ob.bal, Ob.amt]
    intro h
    exact ite_cond_eq_false _ _ (eq_false (Ne.symm h))
  · simp only [trGoalFrame]
    simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.S2, Ob.S1, Ob.sto, Ob.ms, Ob.rcpt, Ob.B, Ob.bal, Ob.amt]
    intro n _ _ h1 h2
    simp only [Env.setI] at *
    simp_all


/-- The goal of one of `transfer`'s obligations at `trEnv`, with no verdict. -/
theorem tr_obligation_discharged {φ : Tm} (hφ : (trHyps, φ) ∈ trObs)
    {s : Storage} (hs : ∀ k, s k < 2 ^ 256) {t a : Nat} (hta : t < 2 ^ 160) (ha : a < 2 ^ 256)
    (hle : a ≤ s senderSlot) (hov : midTo t a s + a < 2 ^ 256) : φ.Holds (trEnv t a s) :=
  trObs_valid _ hφ _ (trHyps_hold s hs t a hta ha hle hov)

/-- `Token.transfer` meets its three ensures clauses on distinct addresses on the stage's scope,
given only injectivity of the mapping slot on address keys. -/
theorem transfer_triple_discharged (inj : HashInj)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnTransfer [(2, 4096)]) (fun _ => True) trPost := by
  have hdep := burnShape_eq
  simp only [burnShape?, hc, Option.some.injEq, Prod.mk.injEq] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep.1
  have hshape := transferShape_eq
  simp only [transferShape?, hc, Option.some.injEq, Option.map_eq_some_iff, Prod.mk.injEq] at hshape
  obtain ⟨f, hf, hlen, hT⟩ := hshape
  have himpl := implements_tree (fn := fnTransfer) hd (by decide) hf hlen hT rfl
  apply triple_of_wp himpl
  rintro _ ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ -
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨t, a, rfl⟩ : ∃ t a, args = [t, a] := by
    match args, hl with
    | [t, a], _ => exact ⟨t, a, rfl⟩
  have ht : t < 2 ^ 256 := hargs t (by simp)
  have ha : a < 2 ^ 256 := hargs a (by simp)
  have hw : argWords 2 ({ calldata := Abi.calldata fnTransfer.sel [t, a], callvalue := 0, storage := σ } : Call) =
      [t, a] := argWords_calldata _ [t, a] hargs 0 σ
  rw [vc_eq, treeModel_run, show fnTransfer.params.length = 2 from rfl, hw]
  set s := initStorage ({ calldata := Abi.calldata fnTransfer.sel [t, a], callvalue := 0, storage := σ } : Call)
    with hs_def
  have hs : ∀ k, s k < 2 ^ 256 := fun k => Generic.slotValue_lt σ k
  unfold resOutcome
  split
  · next hok =>
    intro _
    obtain ⟨hta, hle, hov, -⟩ := tr_success inj s hs t a ht ha hok
    have hb := trStore_eval inj s hs t a ht ha hok
    have hcw : (callerWord : Int) = 8192 := rfl
    have h8 : balArr s 8192 = (s senderSlot : Int) := balArr_caller s
    have hob := fun φ (hφ : (trHyps, φ) ∈ trObs) => tr_obligation_discharged hφ hs hta ha hle hov
    have gFrom := hob trGoalFrom (by simp [trObs])
    have gTo := hob trGoalTo (by simp [trObs])
    have gFrame := hob trGoalFrame (by simp [trObs])
    simp only [trGoalFrom, trGoalTo, trGoalFrame, Tm.Holds, Tm.eval, Tm.evalList, applyOp,
      Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.le0,
      Ob.leA, Ob.bal, Ob.B, Ob.ms, Ob.amt, Ob.rcpt, S2_setI] at gFrom gTo gFrame
    simp only [observe, hw, List.getD_cons_zero, List.getD_cons_succ]
    rw [← hs_def]
    have hsl : solHash callerWord 0 = senderSlot := hash_eq
    refine ⟨fun hne => ?_, fun hne => ?_, fun x hx hx8 hxt => ?_⟩
    · have e : (((transferTree.eval (valOf [t, a] s)).store senderSlot : Nat) : Int) =
          (Ob.S2.eval (trEnv t a s)).toArr 8192 := by
        have := hb callerWord (by decide); rwa [hsl] at this
      have g := gFrom (by simp; omega)
      simp [h8] at g
      simp only [Value.toArr] at e g
      rw [hsl]
      omega
    · have e := hb t hta
      have g := gTo (by simp; omega)
      simp [balArr_nat] at g
      simp only [Value.toArr] at e g
      omega
    · have e := hb x hx
      have hx8' : ¬ (x : Int) = 8192 := by intro h; apply hx8; exact_mod_cast h
      have hxt' : ¬ (x : Int) = t := by omega
      have hxA : (x : Int) ≤ 1461501637330902918203684832716283019655932542975 := by omega
      have g := gFrame x
      simp [balArr_nat, hx8', hxt', hxA, S2_setI] at g
      simp only [Value.toArr] at e g
      omega
  · intro h; simp_all [observe]

/-- info: 'SolidCore.Verify.VC.Token.transfer_triple_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_triple_discharged

end SolidCore.Verify.VC.Token

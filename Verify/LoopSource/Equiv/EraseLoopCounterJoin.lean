import Verify.LoopSource.Equiv.EraseLoopLeastFuel
import Verify.LoopSource.Equiv.EraseLoopCounter
import Verify.LoopSource.Equiv.Counter.Resources

/-!
# The source-resource join, instantiated: a counted loop from its erasure to a constant gas bound

`EraseLoopLeastFuel.lean`'s `BridgeTarget` (`eraseLoop_certified_loops`) gives the driver's whole
`Shapes.Certified` at a constant gas bound from `eraseLoopStmt`, a cut-point certificate `C` with its
obligations `Obl` over the erased tree, the backend's stage, the loop checker and a measure bridge of
the final EVM IR (`Verify.Gas.FixedFuel.Loops`). This module makes it usable with what the driver
generates, and instantiates it for `Counter.bump`.

* `obl_of_eval`, `onTree_of_eval`: obligations and tree properties move between two trees whose
  observables agree on every valuation of a clean storage. The generator's sequents are stated
  over the tree of a function's body summary; the erasure computes its own tree (here with the
  loop's closed form `count + (n - 0 if 0 < n else 0)` and two overflow guards that never fire), and
  only the observables matter to `Obl`.
* `GeneratedTarget`, `eraseLoop_certified_generated`: `BridgeTarget` for the shape the generator
  emits: a `Cut` whose check yields `(le, li)`, sequents `allSeqs` of an invariant `I` and a
  measure `μ` against a tree `T0`, every sequent valid, and `T0` observably equal to the erased
  tree. The record is `recOf I μ`, `toSrc = id`, no MIR-only invariant and no call precondition.
* For `Counter.bump`: the erased tree's observables are the summary tree's (`tree_same`), so the
  generated `Counter/Obl.lean` certificate serves the erasure route; a two-block-per-iteration
  bridge of the final EVM IR `evm7` (`bridge`, `loops`, from its `sym_exec` block facts) gives the
  constant fuel `fixedFuel 2 2 3 K` on every call `bump(a)`, `a ≤ K`.
* `counter_join`: `Counter.bump` certified through `eraseLoop_certified_generated` (hence
  `eraseLoop_certified_loops : BridgeTarget`) at the statement fuel `2 ^ 256 + 8`, with the gas bound
  `K * 1414400 + 3536012`, for every `K ≤ Kmax`; `counter_join_bound`: the same bound as
  `counter_certified_bounded`'s. Neither uses `counter_resources`, `counter_stage` or the loop summary's
  `BodyRuns`: the source runs by `bodyRuns_of_eraseLoop`.

The loop shapes covered are those `eraseLoopStmt` erases (one counted `for` loop per function body,
`Proof/EraseLoop.lean`) whose final EVM IR has one loop header (`FixedFuel.Bridge`: one record, one
header).
-/

namespace Verify.LoopSource.Equiv.EraseLoopJoin
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar

/-! ## Moving obligations between observably equal trees -/

/-- **Obligations depend on the tree only through its observables.** -/
theorem obl_of_eval {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop} {n : Nat}
    {cases : List Facts} {T T0 : Tree} {le li : List (Facts × Out)}
    (h : ∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs)
    (o : Obl L toSrc X A n cases T0 le li) : Obl L toSrc X A n cases T le li where
  entry ρ hl hok hA p hp hh := by
    have hx := o.entry ρ hl hok hA p hp hh
    obtain ⟨F, out⟩ := p
    cases out with
    | exit U =>
      dsimp only at hx ⊢
      rw [h ρ hok]
      exact hx
    | back hs => exact hx
  iter σ hl hok hA hP hX p hp hh := by
    have hx := o.iter σ hl hok hA hP hX p hp hh
    obtain ⟨F, out⟩ := p
    cases out with
    | exit U =>
      dsimp only at hx ⊢
      rw [h (trunc n σ) hok]
      exact hx
    | back hs => exact hx
  facts := o.facts

/-- **Tree properties move the same way.** -/
theorem onTree_of_eval {sel : Nat} {fn : FunctionDef} {ws : List Nat} {T T0 : Tree}
    {Q : Call → Observable → Prop} (h : ∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs)
    (hQ : OnTree sel fn ws T0 Q) : OnTree sel fn ws T Q := by
  intro σ args ha
  rw [h ⟨args, slotValue σ, solHash, callerWord⟩ (slotValue_store σ)]
  exact hQ σ args ha

/-! ## The join, for what the generator emits -/

/-- **The constant-gas join from the erasure and generated obligations.** `BridgeTarget`'s
premises, with the obligations given as the generator emits them: sequents `allSeqs` of an
invariant `I` and a measure `μ` against a tree `T0`, each valid, and `T0`'s observables those of
the erased tree `T` on every clean valuation; `Allowed` and `Post` on `T0`. -/
def GeneratedTarget : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (C : Cut) (ev : EnvFlags) (m : Module) (le li : List (Facts × Out)),
    C.check ev m sel fn.params.length = some (le, li) →
    ∀ (T0 : Tree) (I : List Inv.F) (μ : WExpr) (ss : List Inv.Seq),
    Inv.allSeqs fn.params.length C.cases T0 le li I μ = some ss → (∀ s ∈ ss, s.Valid) →
    (∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs) →
    ∀ (q : Assemble.Program) (code : ByteArray) (scope : Call → Prop) (cert : Assemble.Cert)
      (mx : List Nat),
    Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope →
    (∀ call, SelCall sel fn ws call → scope call) →
    AssembleLoop.checkL q code cert mx = true →
    ∀ (Valid : Call → Prop) (Allowed Post : Call → Observable → Prop),
    (∀ call, Valid call → SelCall sel fn ws call) → (∃ call, Valid call) →
    OnTree sel fn ws T0 Allowed → OnTree sel fn ws T0 Post →
    ∀ (R : LoopRecord) (E B Xs M : Nat),
    (∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B Xs M) →
    AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M) < 2 ^ 64 →
    Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post
      (fun _ => AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M))

/-- **The join for generated obligations**, by `eraseLoop_certified_loops`. -/
theorem eraseLoop_certified_generated : GeneratedTarget := by
  intro fuel c sel fn ws b T hsel hfind hw hret h hT C ev m le li hchk T0 I μ ss hss hv hsame q code
    scope cert mx backend hscope asm Valid Allowed Post hsub hinh hAl hP R E B Xs M loops hfit
  exact LeastFuel.eraseLoop_certified_loops fuel c sel fn ws b T hsel hfind hw hret h hT C ev m le li
    hchk (fun _ => Inv.recOf I μ) id (fun _ => True) (fun _ => True)
    (obl_of_eval hsame (Inv.obl_of_seqs hss hv)) (fun _ _ _ => trivial) q code scope cert mx backend
    hscope asm Valid Allowed Post hsub hinh (onTree_of_eval hsame hAl) (onTree_of_eval hsame hP) R E
    B Xs M loops hfit

/-! ## Counter.bump: the erased tree is the summary tree -/

namespace Counter
open Contracts.VerifyCounter.Source Verify.LoopSource.MirLink

/-- The erasure's iteration count is the argument word. -/
theorem iters_eval (ρ : Val) : EraseLoopCounter.iters.eval ρ = (WExpr.arg 0).eval ρ := by
  have h := (WExpr.arg 0).eval_lt ρ
  have hW : 1 < Generic.wordSize := by decide
  show (if (WExpr.bin .lt (.lit 0) (.arg 0)).eval ρ = 0 then (WExpr.lit 0).eval ρ
    else (WExpr.bin .sub (.arg 0) (.lit 0)).eval ρ) = _
  rw [eval_bin, eval_bin, eval_lit]
  generalize (WExpr.arg 0).eval ρ = x at h ⊢
  simp only [BinOp.eval, Nat.zero_mod]
  by_cases h0 : x = 0
  · subst h0; simp
  · have hpos : 0 < x := Nat.pos_of_ne_zero h0
    simp [hpos, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt h]

/-- The checked contract's `bump` body erases, at the statement's fuel, to `bumpLoopBr`. -/
theorem erased {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    eraseLoopStmt { envOf c.core with facts := argFacts [256] 0 } Contracts.VerifyCounter.Source.fuel
      bumpFn.body (initState bumpFn) = some EraseLoopCounter.bumpLoopBr := by
  have h := EraseLoopCounter.bump_erased c.core.eventDecls c.core.table
  have hE : ({ envOf c.core with facts := argFacts [256] 0 } : EraseEnv) =
      EraseLoopCounter.env c.core.eventDecls c.core.table := by
    simp only [envOf, EraseLoopCounter.env, (shape_of hc).1]
    rfl
  rw [hE]
  exact h

/-- The erased tree exists. -/
theorem loop_tree : ∃ T, brTree bumpFn (argFacts [256] 0) EraseLoopCounter.bumpLoopBr = some T :=
  Option.isSome_iff_exists.mp (by decide +kernel)

/-- **The erased tree and the summary tree give every valuation the same result.** -/
theorem tree_same {TL T0 : Tree} (hL : brTree bumpFn (argFacts [256] 0) EraseLoopCounter.bumpLoopBr = some TL)
    (h0 : brTree bumpFn (argFacts [256] 0) bumpBr = some T0) (ρ : Val) : TL.eval ρ = T0.eval ρ := by
  obtain ⟨A, hA, eA⟩ := brTree_eval bumpFn (argFacts [256] 0) ρ _ TL hL
  obtain ⟨B, hB, eB⟩ := brTree_eval bumpFn (argFacts [256] 0) ρ _ T0 h0
  rw [← eA, ← eB]
  have hovf : EraseLoopCounter.ovf = ovf := rfl
  have hle : EraseLoopCounter.le = Contracts.VerifyCounter.Source.le := rfl
  unfold EraseLoopCounter.bumpLoopBr at hA
  unfold bumpBr at hB
  rw [hovf, hle, guards_eval] at hA
  rw [guards_eval] at hB
  by_cases hg : [ovf].any (fun g => g.eval ρ != 0) = true
  · simp only [hg, ↓reduceIte] at hA hB
    obtain rfl := Option.some.inj (hA.symm.trans hB)
    rfl
  simp only [hg] at hA hB
  simp only [Br.eval] at hA hB
  by_cases hv : Contracts.VerifyCounter.Source.le.eval ρ = 0
  · simp only [hv, ↓reduceIte] at hA hB
    obtain rfl := Option.some.inj (hA.symm.trans hB)
    rfl
  simp only [hv, ↓reduceIte] at hA hB
  have hsum : (WExpr.bin .add (.init 0) EraseLoopCounter.iters).eval ρ =
      (WExpr.bin .add (.init 0) (.arg 0)).eval ρ := by
    rw [eval_bin, eval_bin, iters_eval]
  have hno : ovf.eval ρ = 0 := by simpa [List.any_cons, List.any_nil] using hg
  have hg2 : ([WExpr.bin .lt (.bin .add (.init 0) EraseLoopCounter.iters) (.init 0),
      WExpr.bin .lt (.bin .add (.lit 0) EraseLoopCounter.iters) (.lit 0)].any
        fun g => g.eval ρ != 0) = false := by
    have h1 : (WExpr.bin .lt (.bin .add (.init 0) EraseLoopCounter.iters) (.init 0)).eval ρ = 0 := by
      rw [eval_bin, hsum, ← eval_bin]
      exact hno
    have h2 : (WExpr.bin .lt (.bin .add (.lit 0) EraseLoopCounter.iters) (.lit 0)).eval ρ = 0 := by
      simp [eval_bin, eval_lit, BinOp.eval]
    simp [h1, h2]
  rw [guards_eval, hg2] at hA
  simp only [Br.eval, Bool.false_eq_true, ite_false] at hA
  obtain rfl : A = Tree.halt true [] [(.lit 0, .bin .add (.init 0) EraseLoopCounter.iters)] [] := by
    simp [leafTree, bumpFn, EraseLoopCounter.SF, retsOk] at hA
    exact hA.symm
  obtain rfl : B = Tree.halt true [] [(.lit 0, .bin .add (.init 0) (.arg 0))] [] := by
    simp [leafTree, bumpFn, SF, retsOk] at hB
    exact hB.symm
  simp only [Tree.eval, ite_true]
  congr 1
  funext k
  simp only [Writes.store, hsum]

/-! ## Counter.bump: the bridge of the final EVM IR -/

/-- The machine's record: one header word, the iterations left; no invariant beyond it. -/
def rec : LoopRecord :=
  { H := { scopes := [], writes := [], logs := [] }, P := fun _ => True,
    m := fun σ => (WExpr.arg 0).eval σ, c := .arg 0, bb := .leaf (.reverted .empty) }

/-- The valuation of `k` iterations left. -/
def valOf (k : Nat) : Val := ⟨[k], fun _ => 0, fun _ _ => 0, 0⟩

theorem valOf_eval {k : Nat} (hk : k < 2 ^ 256) : (WExpr.arg 0).eval (valOf k) = k := by
  simp only [WExpr.eval, valOf, List.getD_cons_zero]
  exact Nat.mod_eq_of_lt hk

open SolarTV.Export.Counter Verify.LoopSource.Equiv.CounterResources Verify.Gas.FixedFuel in
/-- A header configuration of `evm7` (block 8, the stack `[f, h, c, w]` with `0 - h` the
iterations left and `c + left` not wrapping), or, with no iteration left, a configuration that ends
within the exit's three blocks (the entry's reverts). -/
abbrev At (o : Oracle) (call : Call) (σ : Val) (x : Nat × EVM.Stack × SolarTV.Machine.State) : Prop :=
  ((WExpr.arg 0).eval σ = 0 ∧ ∃ r, iterate (EVM.Program.block o call evm7) 3 x = some r) ∨
    ∃ (f h c w : EvmRules.Word) (s : SolarTV.Machine.State), x = (8, [f, h, c, w], s) ∧
      (0 - h).toNat = (WExpr.arg 0).eval σ ∧ c.toNat + (WExpr.arg 0).eval σ < 2 ^ 256

open SolarTV.Export.Counter Verify.LoopSource.Equiv.CounterResources Verify.Gas.FixedFuel in
/-- **The bridge**: two blocks per iteration (8, 7), three to the end. -/
def bridge (o : Oracle) (call : Call) : Bridge rec (EVM.Program.block o call evm7) 2 3 where
  At := At o call
  iter := by
    intro σ x hx _ hc
    change (WExpr.arg 0).eval σ ≠ 0 at hc
    rcases hx with ⟨h0, _⟩ | ⟨f, h, c, w, s, rfl, hm, hcw⟩
    · exact absurd h0 hc
    · obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hc
      have hlt := (WExpr.arg 0).eval_lt σ
      rw [hm'] at hm hcw hlt
      have hmw : m < 2 ^ 256 := by unfold Generic.wordSize at hlt; omega
      refine ⟨valOf m, (8, [1, h + 1, c + 1, w], s), ⟨trivial, ?_, trivial, ?_⟩,
        Or.inr ⟨1, h + 1, c + 1, w, s, rfl, ?_, ?_⟩, ?_⟩
      · change (WExpr.arg 0).eval σ ≠ 0
        rw [hm']; omega
      · change (WExpr.arg 0).eval (valOf m) < (WExpr.arg 0).eval σ
        rw [valOf_eval hmw, hm']; omega
      · rw [valOf_eval hmw]; exact neg_toNat_succ hm
      · rw [valOf_eval hmw, toNat_succ_of hcw]; omega
      · exact ⟨2, Nat.le_refl _, .cont (b8_loop o call f h c w s (by bv_omega))
          (.cont (b7 o call f h c w s (succ_ne_zero_of hcw)) (.refl _))⟩
  done := by
    intro σ x hx _ hc
    change (WExpr.arg 0).eval σ = 0 at hc
    rcases hx with ⟨_, hr⟩ | ⟨f, h, c, w, s, rfl, hm, hcw⟩
    · exact hr
    · rw [hc] at hm hcw
      obtain ⟨r, hr⟩ := header_ends o call 0 f h c w s hm hcw
      exact ⟨r, iterate_mono_le (by omega) hr⟩

open SolarTV.Export.Counter Verify.LoopSource.Equiv.CounterResources Verify.Gas.FixedFuel in
/-- **Every bounded call has the bridge**: the entry reaches a configuration of `At` within two
blocks (0, 6), at a valuation whose measure is the argument, at most `K`. -/
theorem loops (o : Oracle) {K : Nat} {call : Call}
    (hv : Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K call) :
    Loops (EVM.Program.block o call evm7) (0, [], SolarTV.Machine.State.initial call) rec 2 2 3 K := by
  obtain ⟨σ, a, haK, ha, rfl⟩ := hv
  obtain ⟨hcv, hsz, hn, hsel⟩ := bump_facts (σ := σ) ha
  generalize bumpCall σ a = call at hcv hsz hn hsel ⊢
  have hz : ¬BitVec.ofNat 256 call.calldata.size < 36 := by rw [hsz]; decide
  have hb0 := b0' o call hcv hsel
  refine ⟨bridge o call, ?_⟩
  by_cases ho : EvmRules.Evm.add ((SolarTV.Machine.State.initial call).storage 0) (calldataWord call 4) <
      (SolarTV.Machine.State.initial call).storage 0
  · refine ⟨valOf 0, _, ⟨2, Nat.le_refl _, .cont hb0 (.cont (b6_ovf o call _ _ hz ho) (.refl _))⟩,
      show At o call (valOf 0) _ from Or.inl ⟨valOf_eval (by decide), ends_of_halts (b2 o call _ _ _ _ _) 2⟩,
      trivial, ?_⟩
    change (WExpr.arg 0).eval (valOf 0) ≤ K
    rw [valOf_eval (by decide)]; omega
  by_cases hl : (SolarTV.Machine.State.initial call).storage 1 <
      EvmRules.Evm.add ((SolarTV.Machine.State.initial call).storage 0) (calldataWord call 4)
  · refine ⟨valOf 0, _, ⟨2, Nat.le_refl _, .cont hb0 (.cont (b6_over o call _ _ hz ho hl) (.refl _))⟩,
      show At o call (valOf 0) _ from Or.inl ⟨valOf_eval (by decide), ends_of_halts (b12 o call _ _ _ _) 2⟩,
      trivial, ?_⟩
    change (WExpr.arg 0).eval (valOf 0) ≤ K
    rw [valOf_eval (by decide)]; omega
  have hno : ((SolarTV.Machine.State.initial call).storage 0).toNat + a < 2 ^ 256 := by
    simp only [EvmRules.Evm.add] at ho
    rw [← hn]
    bv_omega
  have hm : (0 - EvmRules.Evm.sub 0 (calldataWord call 4)).toNat = a := by
    simp only [EvmRules.Evm.sub]
    rw [← hn]
    bv_omega
  refine ⟨valOf a, _, ⟨2, Nat.le_refl _, .cont hb0 (.cont (b6_pass o call _ _ hz ho hl) (.refl _))⟩,
    show At o call (valOf a) _ from
      Or.inr ⟨0, _, _, _, _, rfl, by rw [valOf_eval ha]; exact hm, by rw [valOf_eval ha]; exact hno⟩,
    trivial, ?_⟩
  change (WExpr.arg 0).eval (valOf a) ≤ K
  rw [valOf_eval ha]; exact haK

/-! ## Counter.bump through the join -/

open SolarTV.Export.Counter Verify.LoopSource.Equiv.CounterResources Verify.Gas.FixedFuel in
/-- **Counter.bump, certified through the erasure's constant-gas join**: for every `K ≤ Kmax`,
the driver's whole `Shapes.Certified` statement of the source (at the statement fuel `2 ^ 256 + 8`)
and the exact emitted runtime `code` on the calls `bump(a)`, `a ≤ K`, with `bump`'s postcondition and
the gas bound `K * 1414400 + 3536012`. No premise. -/
theorem counter_join {K : Nat} (hK : K ≤ Kmax) :
    ∃ c, contract? = .ok c ∧
      Shapes.Certified stmtSem c SolarTV.Milestone.X.code
        (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K) (fun _ _ => True) BumpPost
        (fun _ => K * 1414400 + 3536012) := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨TL, hTL⟩ := loop_tree
  have hsame : ∀ ρ : Val, ρ.Ok → (TL.eval ρ).obs = (CounterObl.T.eval ρ).obs :=
    fun ρ _ => congrArg Res.obs (tree_same hTL CounterObl.tree ρ)
  have h := eraseLoop_certified_generated Contracts.VerifyCounter.Source.fuel c bumpSel bumpFn [256]
    EraseLoopCounter.bumpLoopBr TL (by decide) (shape_of hc).2.2 rfl rfl (erased hc) hTL
    Generated.Counter.cut .off stage0 CounterObl.le CounterObl.li CounterObl.leaves CounterObl.T
    CounterObl.I CounterObl.μ CounterObl.ss CounterObl.seqs CounterObl.valid hsame evm7
    SolarTV.Milestone.X.code _ SolarTV.Milestone.X.cert SolarTV.Milestone.X.maxs
    (SolarTV.Milestone.X.counterLoop_mir_to_evmir Shapes.oracle) (fun _ _ => trivial)
    SolarTV.Milestone.X.check_ok (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K)
    (fun _ _ => True) BumpPost
    (fun call hv => by
      obtain ⟨σ, a, -, ha, rfl⟩ := hv
      exact ⟨σ, [a], args_one ha, rfl⟩)
    (Verify.LoopSource.Equiv.CounterGas.bounded_inhabited K) (fun _ _ _ => trivial)
    (onTree_of tree_post CounterObl.tree) rec 2 2 3 K (fun call hv => loops Shapes.oracle hv)
    (G_lt hK)
  refine ⟨c, hc, ?_⟩
  have hG : (fun _ : Call => AssembleLoop.gasBoundL SolarTV.Milestone.X.cert (fixedFuel 2 2 3 K)) =
      fun _ => K * 1414400 + 3536012 := funext fun _ => G_eq K
  rw [← hG]
  exact h

/-- **The join's bound is the bounded receipt's**: `counter_certified_bounded`'s gas function
`fun _ => G K` is the join's `fun _ => K * 1414400 + 3536012`. -/
theorem counter_join_bound (K : Nat) :
    (fun _ : Call => Verify.LoopSource.Equiv.CounterResources.G K) = fun _ => K * 1414400 + 3536012 :=
  funext fun _ => Verify.LoopSource.Equiv.CounterResources.G_eq K

/-- **`counter_certified_bounded`'s exact statement, through the join**: the same contract, code,
calls, postcondition and gas function `fun _ => G K`, from `counter_join`. -/
theorem counter_join_receipt {K : Nat} (hK : K ≤ Verify.LoopSource.Equiv.CounterResources.Kmax) :
    ∃ c, contract? = .ok c ∧
      Shapes.Certified stmtSem c SolarTV.Milestone.X.code
        (Verify.LoopSource.Equiv.CounterGas.BumpCallBounded K) (fun _ _ => True) BumpPost
        (fun _ => Verify.LoopSource.Equiv.CounterResources.G K) := by
  rw [counter_join_bound K]
  exact counter_join hK

end Counter

end Verify.LoopSource.Equiv.EraseLoopJoin

/-- info: 'Verify.LoopSource.Equiv.EraseLoopJoin.obl_of_eval' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.EraseLoopJoin.obl_of_eval

/-- info: 'Verify.LoopSource.Equiv.EraseLoopJoin.eraseLoop_certified_generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.EraseLoopJoin.eraseLoop_certified_generated

/-- info: 'Verify.LoopSource.Equiv.EraseLoopJoin.Counter.tree_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.EraseLoopJoin.Counter.tree_same

/-- info: 'Verify.LoopSource.Equiv.EraseLoopJoin.Counter.counter_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.EraseLoopJoin.Counter.counter_join

/-- info: 'Verify.LoopSource.Equiv.EraseLoopJoin.Counter.counter_join_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.EraseLoopJoin.Counter.counter_join_receipt

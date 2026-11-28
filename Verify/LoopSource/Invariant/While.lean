import Verify.LoopSource.Proof.EraseLoop

/-!
# `while` loops through an invariant: the source side of the loop join

`eraseLoopStmt` (`Proof/EraseLoop.lean`) erases one shape of loop, a counted `for` loop stepping
its words by `+ 1`, by computing its closed form. This module erases a `while` loop through an
**invariant** instead: the closed form is not computed, it is only named (the words after the loop,
`WhileData.exit`) and proved from the invariant, a measure and the loop's erased words.

The loop is described by data (`WhileData`, untrusted: a solver, a generator or a person writes
it). Some of it is **proposed** and only checked for consistency, some is **recomputed** from the
statement and compared by equality, and `exit` is justified by the obligations alone:

* proposed: `S1`, the state before the loop, which `eraseWhile` requires to be exactly the
  symbolic state the erasure reaches at the loop; `slots`, the constant slots an iteration writes;
  and `k`, the body's fuel. Neither the slots nor a least `k` is inferred: the **header** is
  `header base S1 slots` (`EraseLoop.lean`), `S1` with a fresh word `.arg (base + j)` for each
  local and each proposed slot;
* recomputed by `check` at that header: `c`, the condition's word (the condition must erase with
  no overflow guard), and `gs`, `S2`, the body run once with fuel `k` (`eraseStep`: the generic
  erasure with `x++` and `x--` on a local word): a tree of overflow guards before one normal end
  `S2`. Each is compared with the proposed value by `DecidableEq`, and `S2` must be the header
  with each fresh word replaced by the word `S2` shows for it (`step`);
* never read by `check`: `exit`, the words after the loop over the words before it. Changing it
  leaves the structural check unchanged; only `Obl.exit` (below) ties it to the loop.

The obligations (`Obl`) are an invariant `I ρ σ` and a measure `μ ρ σ` of header valuations
`σ = extV ρ base len f` over the call valuation `ρ`, and facts about words only:

* **initiation**: `I` holds at the valuation the state before the loop shows (`headVal`), where
  the measure is below `loopFuel`;
* **exit**: where `I` holds and `c` is zero, every fresh word is its `exit` word;
* **iteration**: where `I` holds and `c` is not zero, no guard of the body fires, `I` holds after
  the step (**preservation**), and the measure falls.

`runs_while` proves the `while` statement ends normally in the header with the `exit` words, from
`whileLoop_of_erased` (`Proof/LoopErased.lean`): the obligations above give `WhileObl` with the
invariant "some words `f` with `I`" and the loop's measure. `eraseWhile` erases a body whose loops
are `while` loops described by one `WhileData`, and `bodyRuns_of_eraseWhile` gives `BodyRuns`, the
premise the loop join takes (`Invariant/Join.lean`).

Outside the shape the erasure is `none`: `for` loops, a loop at a state other than `S1`, a
condition that erases with an overflow guard or has a side effect, a body that does not erase
(nested loops, `break`/`continue`, which the interpreter runs but this erasure cannot represent, a
return or a revert other than an overflow guard, internal calls the erasure has no arm for), a body
whose end is not the header with its own words, and too little fuel. A checked body guard models
`Panic(0x11)`, not wrapping: `Obl.guards` requires the invariant to prove every guard zero on a
taken iteration. Nothing about the loop is assumed: `Obl` is a hypothesis the caller proves, about
words.
-/

namespace Verify.LoopSource.Invariant
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-! ## `x--` on a local word -/

theorem binOf_sub : binOf .sub = some .sub := rfl

/-- `target--` on a target that resolves to `lv`, which holds the word `old`: `Panic(0x11)` when
`old` is zero, else `old - 1` written back, which leaves `rt'` related to `S'`. -/
theorem eval_dec (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) (post : Bool) {target : Expr} {lv : ResolvedLValue}
    {old : WExpr} {rt' : Runtime} {S' : SymState}
    (hres : ∀ F, target.orderFuel < F → Expr.resolveLValueFuel F ctx rt target = pure (lv, rt))
    (hread : ResolvedLValue.read ctx rt lv = .ok (.word (old.eval ρ)))
    (hwrite : ResolvedLValue.write ctx rt lv (.word ((WExpr.bin .sub old (.lit 1)).eval ρ)) = .ok rt')
    (hrel' : StmtRel ρ E ctx rt' S') :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.incDec .sub post (some (.uint 256)) target)) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((guards (overflow .sub old (.lit 1)).toList (.leaf (.normal S'))).eval ρ) := by
  have happ := apply_erased ρ binOf_sub old (.lit 1)
  rw [← one_eq] at happ
  have hcleq : ctx.checked = true := hrel.checked
  have hcl : ValueCleanup.apply true (.uint 256) (.word ((WExpr.bin .sub old (.lit 1)).eval ρ)) =
      .ok (.word ((WExpr.bin .sub old (.lit 1)).eval ρ)) := uintCleanup_256 _ (WExpr.eval_lt ρ _)
  rw [Stmt.eval]
  simp only [Expr.eval, Expr.orderFuel]
  rw [Expr.evalFuel, hres _ (by omega)]
  simp only [pure_bind_sol]
  rw [guards_eval]
  by_cases hg : (overflow .sub old (.lit 1)).toList.any (fun g => g.eval ρ != 0) = true
  · have hE : ResolvedLValue.applyIncDecCleanup ctx rt lv .sub post (.uint 256) =
        .error (.panic 0x11) := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, ↓reduceIte]
    rw [hE]
    simp only [hg, ↓reduceIte]
    exact ⟨.reverted rt (.panic 0x11), rfl, by simp only [failCode_overflow]; rfl⟩
  · have hE : ∃ v, ResolvedLValue.applyIncDecCleanup ctx rt lv .sub post (.uint 256) =
        .ok (v, rt') := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, Bool.false_eq_true, ↓reduceIte,
        hcl, hwrite]
      cases post <;> exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := hE
    rw [hv]
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, hrel'⟩

/-- The leaf of `x--` on a local word `x` whose word is `old`, `L'` the scopes with `x` set. -/
def decVarBr (old : WExpr) (L' : Scopes) (S : SymState) : Br :=
  guards (overflow .sub old (.lit 1)).toList (.leaf (.normal { S with scopes := L' }))

/-- **`x--` on a local word.** -/
theorem eval_decVar (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) (post : Bool) {x : String} {old : WExpr} {L' : Scopes}
    (hold : S.word? x = some old)
    (hL : S.setW x (.bin .sub old (.lit 1)) = some L') :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.incDec .sub post (some (.uint 256)) (.var x))) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((decVarBr old L' S).eval ρ) := by
  have hx : rt.lookupLocal? x = some (.word (old.eval ρ)) := hrel.expr.locals x old hold
  have hbase : rt.lookupStorageBase? x = none := by simp [Runtime.lookupStorageBase?, hx]
  obtain ⟨hxw, hL0⟩ := SymState.setW_spec hL
  refine eval_dec ρ E ctx rt S hrel n post (lv := .local x) (rt' := { rt with locals := L'.map (frameOfT ρ S.tags) })
    (S' := { S with scopes := L' })
    (fun F hF => ?_) ?_ ?_ { hrel with frames := rfl }
  · obtain ⟨m, rfl⟩ : ∃ m, F = m + 1 := ⟨F - 1, by omega⟩
    simp only [Expr.resolveLValueFuel, hbase, hx]
  · simp [ResolvedLValue.read, ResolvedLValue.readRaw, hx, Runtime.derefMemoryValue, bind,
      Except.bind]
  · simp [ResolvedLValue.write, assignLocal_word hrel.frames hxw hL0]

/-- `x--` on a local word runs as `decVarBr`. -/
theorem stmtRuns_decVar {E : EraseEnv} {ctx : Context} {S : SymState} (n : Nat) (pst : Bool)
    {x : String} {old : WExpr} {L' : Scopes} (hold : S.word? x = some old)
    (hL : S.setW x (.bin .sub old (.lit 1)) = some L') :
    StmtRuns E (n + 1) ctx (.exprStmt (.incDec .sub pst (some (.uint 256)) (.var x))) S
      (decVarBr old L' S) :=
  fun σ rt hrel => eval_decVar σ E ctx rt S hrel n pst hold hL

/-! ## The loop-free erasure with steps -/

/-- `x--` (or `--x`) of a `uint256`: whether it is postfix, and its target. -/
def decOf? : Stmt → Option (Bool × Expr)
  | .exprStmt (.incDec .sub pst (some (.uint 256)) tgt) => some (pst, tgt)
  | _ => none

theorem decOf?_spec {s : Stmt} {pst : Bool} {tgt : Expr} (h : decOf? s = some (pst, tgt)) :
    s = .exprStmt (.incDec .sub pst (some (.uint 256)) tgt) := by
  unfold decOf? at h
  split at h <;> cases h
  rfl

/-- **The loop-free erasure with steps**: `eraseInc` (the generic erasure with `x++`), with blocks
erased by itself and `x--` of a local word (`decVarBr`). -/
def eraseStep (E : EraseEnv) : Nat → Stmt → SymState → Option Br
  | 0, _, _ => none
  | n + 1, s, S =>
    match s with
    | .block ss => do
      let b ← eraseSeq (eraseStep E n) ss S.push
      some (b.mapS SymState.pop)
    | s =>
      match decOf? s with
      | some (_, .var x) => do
        let old ← S.word? x
        let L' ← S.setW x (.bin .sub old (.lit 1))
        some (decVarBr old L' S)
      | _ => eraseInc E (n + 1) s S

/-- **A statement runs as its `eraseStep` erasure.** -/
theorem runs_eraseStep (E : EraseEnv) (ctx : Context) :
    ∀ n s S b, eraseStep E n s S = some b → StmtRuns E n ctx s S b
  | 0, _, _, _, h => by simp [eraseStep] at h
  | n + 1, s, S, b, h => by
    unfold eraseStep at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b1, h1, rfl⟩ := h
      exact runs_block (runs_eraseStep E ctx n) h1
    · split at h
      · rename_i pst x hdec
        obtain rfl := decOf?_spec hdec
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨old, hold, L', hL, rfl⟩ := h
        exact stmtRuns_decVar n pst hold hL
      · exact runs_eraseInc E ctx (n + 1) s S b h

/-! ## The loop's data and its check -/

/-- **A `while` loop's data** (untrusted): `S1`, `slots`, `k` and `exit` are proposed; `check`
recomputes `c`, `gs` and `S2` at the proposed header and fuel and compares them by equality; it
never reads `exit`, which `Obl.exit` justifies. -/
structure WhileData where
  /-- The state before the loop. -/
  S1 : SymState
  /-- The constant slots an iteration writes. -/
  slots : List Nat
  /-- The body's fuel. -/
  k : Nat
  /-- The condition's word at the header. -/
  c : WExpr
  /-- The body's overflow guards at the header. -/
  gs : List WExpr
  /-- The body's normal end at the header. -/
  S2 : SymState
  /-- The words after the loop, over the words before it, in the header's order. -/
  exit : List WExpr
  deriving Repr

namespace WhileData

/-- The first fresh word: above every argument word of `S1` and of the facts. -/
def base (E : EraseEnv) (wd : WhileData) : Nat := max (maxArgS wd.S1) (maxArgF E.facts)

/-- The number of fresh words. -/
def len (wd : WhileData) : Nat := (entries wd.S1 wd.slots).length

/-- **The header**: `S1` with fresh words for its locals and the slots. -/
def H (E : EraseEnv) (wd : WhileData) : SymState := header (wd.base E) wd.S1 wd.slots

/-- The word fresh word `j` steps to, over the header: the word `S2` shows for it. -/
def step (wd : WhileData) (j : Nat) : WExpr := (entries wd.S2 wd.slots).getD j (.lit 0)

/-- The word fresh word `j` holds after the loop, over the words before it. -/
def exitθ (wd : WhileData) (j : Nat) : WExpr := wd.exit.getD j (.lit 0)

/-- The header valuation of the words `f` over `ρ`. -/
def at_ (E : EraseEnv) (wd : WhileData) (ρ : Val) (f : Nat → Nat) : Val := extV ρ (wd.base E) wd.len f

/-- The words of the step from the header valuation `σ`. -/
def stepV (wd : WhileData) (σ : Val) (j : Nat) : Nat := (wd.step j).eval σ

/-- **The tree after the loop**: the header with the `exit` words. -/
def exitBr (E : EraseEnv) (wd : WhileData) : Br :=
  .leaf (.normal (instS (wd.base E) wd.len wd.exitθ (wd.H E)))

end WhileData

/-- **The check**: `S1` and the facts are below `base`; the condition erases at the header (built
from the proposed `S1` and `slots`) to `c` with no guard; the body erases at the header, with the
proposed fuel `k`, to the guards `gs` before the end `S2`; and `S2` is the header with each fresh
word replaced by its `step`. It does not read `exit`; `eraseWhile` adds that `S1` is the state the
erasure reaches at the loop. -/
def check (E : EraseEnv) (wd : WhileData) (cnd : Expr) (body : Stmt) : Bool :=
  belowS (wd.base E) wd.S1 && factsBelow (wd.base E) E.facts &&
    decide (eraseExpr E.fields (wd.H E) cnd = some ([], wd.c)) &&
    decide (eraseStep E wd.k body (wd.H E) = some (guards wd.gs (.leaf (.normal wd.S2)))) &&
    decide (wd.S2 = instS (wd.base E) wd.len wd.step (wd.H E))

/-! ## The obligations -/

/-- **The obligations of a `while` loop's data** for an invariant `I ρ σ` and a measure `μ ρ σ` of
header valuations `σ` over the call valuation `ρ`: facts about words. -/
structure Obl (E : EraseEnv) (wd : WhileData) (I : Val → Val → Prop) (μ : Val → Val → Nat) :
    Prop where
  /-- Initiation: the invariant holds before the loop. -/
  init : ∀ ρ, ρ.Ok → E.facts.Hold ρ → I ρ (headVal ρ (wd.base E) wd.S1 wd.slots)
  /-- The measure before the loop is below the loop's fuel. -/
  bound : ∀ ρ, ρ.Ok → E.facts.Hold ρ → μ ρ (headVal ρ (wd.base E) wd.S1 wd.slots) < loopFuel
  /-- Exit: where the condition is zero, the words are the `exit` words. -/
  exit : ∀ ρ (f : Nat → Nat), ρ.Ok → E.facts.Hold ρ → (∀ j, f j < Generic.wordSize) → I ρ (wd.at_ E ρ f) →
    wd.c.eval (wd.at_ E ρ f) = 0 → ∀ j, j < wd.len → f j = (wd.exitθ j).eval ρ
  /-- Where the condition is not zero, no overflow guard of the body fires. -/
  guards : ∀ ρ (f : Nat → Nat), ρ.Ok → E.facts.Hold ρ → (∀ j, f j < Generic.wordSize) → I ρ (wd.at_ E ρ f) →
    wd.c.eval (wd.at_ E ρ f) ≠ 0 → ∀ g ∈ wd.gs, g.eval (wd.at_ E ρ f) = 0
  /-- Preservation: the invariant holds after the step. -/
  pres : ∀ ρ (f : Nat → Nat), ρ.Ok → E.facts.Hold ρ → (∀ j, f j < Generic.wordSize) → I ρ (wd.at_ E ρ f) →
    wd.c.eval (wd.at_ E ρ f) ≠ 0 → I ρ (wd.at_ E ρ (wd.stepV (wd.at_ E ρ f)))
  /-- The measure falls. -/
  dec : ∀ ρ (f : Nat → Nat), ρ.Ok → E.facts.Hold ρ → (∀ j, f j < Generic.wordSize) → I ρ (wd.at_ E ρ f) →
    wd.c.eval (wd.at_ E ρ f) ≠ 0 → μ ρ (wd.at_ E ρ (wd.stepV (wd.at_ E ρ f))) < μ ρ (wd.at_ E ρ f)

/-! ## Soundness -/

/-- The invariant `whileLoop_of_erased` takes: some words `f` with `I`. -/
def HeadP (E : EraseEnv) (wd : WhileData) (I : Val → Val → Prop) (ρ σ : Val) : Prop :=
  ∃ f, (∀ j, f j < Generic.wordSize) ∧ σ = wd.at_ E ρ f ∧ I ρ σ

/-- **The obligations give `WhileObl`** at the header, for the call valuation `ρ`, with the exit
condition "the header with the `exit` words". -/
theorem whileObl_of_obl {E : EraseEnv} {wd : WhileData} {I : Val → Val → Prop}
    {μ : Val → Val → Nat} (ho : Obl E wd I μ) {ctx : Context} {cnd : Expr} {body : Stmt}
    (hchk : check E wd cnd body = true) {ρ : Val} (hok : ρ.Ok) (hfacts : E.facts.Hold ρ) :
    WhileObl wd.k E ctx cnd body (wd.H E) (HeadP E wd I ρ) (μ ρ)
      (fun r => LeafRel ρ E ctx r ((wd.exitBr E).eval ρ)) wd.c
      (guards wd.gs (.leaf (.normal wd.S2))) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨_, hK⟩, hc⟩, hb⟩, hS2⟩ := hchk
  refine ⟨hc, runs_eraseStep E ctx wd.k body _ _ hb, ?_, ?_⟩
  · rintro σ rt ⟨f, hf, rfl, hI⟩ hrel hz
    have hx := ho.exit ρ f hok hfacts hf hI hz
    have he : wd.at_ E ρ f = extV ρ (wd.base E) wd.len (fun j => (wd.exitθ j).eval ρ) :=
      extV_congr ρ _ _ hx
    rw [he] at hrel
    exact inst_of_rel hK hrel
  · rintro σ ⟨f, hf, rfl, hI⟩ hnz
    have hg := ho.guards ρ f hok hfacts hf hI hnz
    have hany : (wd.gs.any fun g => g.eval (wd.at_ E ρ f) != 0) = false := by
      simp only [List.any_eq_false, bne_iff_ne, ne_eq, Decidable.not_not]
      exact hg
    rw [guards_eval, hany]
    simp only [Bool.false_eq_true, ↓reduceIte, Br.eval, IterEnd]
    have hσ' : extV (wd.at_ E ρ f) (wd.base E) wd.len (wd.stepV (wd.at_ E ρ f)) =
        wd.at_ E ρ (wd.stepV (wd.at_ E ρ f)) := extV_extV ρ _ _ _ _
    refine ⟨wd.at_ E ρ (wd.stepV (wd.at_ E ρ f)),
      ⟨_, fun j => WExpr.eval_lt _ _, rfl, ho.pres ρ f hok hfacts hf hI hnz⟩,
      ho.dec ρ f hok hfacts hf hI hnz, fun rt h => ?_⟩
    rw [hS2] at h
    have := rel_of_inst hK h
    rw [← hσ']
    exact this

/-- **A `while` loop whose data checks and whose obligations hold runs to the header with the
`exit` words**, at every statement fuel above `k + loopFuel`. -/
theorem runs_while {E : EraseEnv} {wd : WhileData} {I : Val → Val → Prop} {μ : Val → Val → Nat}
    (ho : Obl E wd I μ) {ctx : Context} {n : Nat} {cnd : Expr} {body : Stmt}
    (hk : wd.k + loopFuel ≤ n) (hchk : check E wd cnd body = true) :
    StmtRuns E (n + 1) ctx (.whileLoop cnd body) wd.S1 (wd.exitBr E) := by
  intro ρ rt hrel
  have hchk' := hchk
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hchk'
  obtain ⟨⟨⟨⟨hS, hK⟩, _⟩, _⟩, _⟩ := hchk'
  have hobl := whileObl_of_obl (ctx := ctx) ho hchk hrel.ok hrel.facts
  have hrel0 := rel_header wd.slots hS hK hrel
  have hp0 : HeadP E wd I ρ (headVal ρ (wd.base E) wd.S1 wd.slots) :=
    ⟨_, fun j => WExpr.eval_lt _ _, rfl, ho.init ρ hrel.ok hrel.facts⟩
  have hb := ho.bound ρ hrel.ok hrel.facts
  exact whileLoop_of_erased hobl hp0 hrel0 (n + 1) (by omega)

/-! ## The erasure -/

/-- **The erasure of a statement with `while` loops described by `wd`**, with fuel `n`: blocks
erased by itself, a `while` loop at the state `wd.S1` whose data checks to the header with its
`exit` words (its body with `wd.k` fuel, `loopFuel` below the statement's), and every other
statement by `eraseStep`. -/
def eraseWhile (E : EraseEnv) (wd : WhileData) : Nat → Stmt → SymState → Option Br
  | 0, _, _ => none
  | n + 1, s, S =>
    match s with
    | .block ss => do
      let b ← eraseSeq (eraseWhile E wd n) ss S.push
      some (b.mapS SymState.pop)
    | .whileLoop cnd body =>
      if S = wd.S1 ∧ wd.k + loopFuel ≤ n ∧ check E wd cnd body = true then some (wd.exitBr E)
      else none
    | s => eraseStep E (n + 1) s S

/-- **A statement runs as its `eraseWhile` erasure**, when the loop's obligations hold. -/
theorem runs_eraseWhile {E : EraseEnv} {wd : WhileData} {I : Val → Val → Prop}
    {μ : Val → Val → Nat} (ho : Obl E wd I μ) (ctx : Context) :
    ∀ n s S b, eraseWhile E wd n s S = some b → StmtRuns E n ctx s S b
  | 0, _, _, _, h => by simp [eraseWhile] at h
  | n + 1, s, S, b, h => by
    unfold eraseWhile at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b1, h1, rfl⟩ := h
      exact runs_block (runs_eraseWhile ho ctx n) h1
    · split at h
      · rename_i hc
        obtain ⟨rfl, hk, hchk⟩ := hc
        cases h
        exact runs_while ho hk hchk
      · cases h
    · exact runs_eraseStep E ctx (n + 1) s S b h

/-- **A body with an invariant-carrying `while` loop runs as its erasure**: `BodyRuns` from
`eraseWhile` and the loop's obligations. -/
theorem bodyRuns_of_eraseWhile {E : EraseEnv} {wd : WhileData} {I : Val → Val → Prop}
    {μ : Val → Val → Nat} (ho : Obl E wd I μ) {fuel : Nat} {fn : FunctionDef} {b : Br}
    (h : eraseWhile E wd fuel fn.body (initState fn) = some b) : BodyRuns E fuel fn b :=
  fun ρ ctx rt hrel => runs_eraseWhile ho ctx fuel fn.body (initState fn) b h ρ rt hrel

end Verify.LoopSource.Invariant

/-- info: 'Verify.LoopSource.Invariant.runs_eraseStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.runs_eraseStep

/-- info: 'Verify.LoopSource.Invariant.runs_while' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.runs_while

/-- info: 'Verify.LoopSource.Invariant.bodyRuns_of_eraseWhile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.bodyRuns_of_eraseWhile

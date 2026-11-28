import SolidCore.Refinement.Generic.Loop

/-!
# Increments of the loop fragment, and moving a relation between symbolic states

`i++` and `count++` on `uint256` words, the updates of most loops, as erasure leaves:
`eval_incVar` (a local word) and `eval_incField` (a word storage field) run SolidCore's
`Expr.incDec` statement under `StmtRel` to the leaf the overflow guard selects: `Panic(0x11)`
when the old word is `2 ^ 256 - 1`, else the old word plus one written back.

`StmtRel.congr` moves `StmtRel` to another valuation and symbolic state that show the same
locals, storage, logs and caller: what a loop's invariant needs to name the state at its header with
fresh words for the values the loop changes.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source SolidCore.Refinement.Generic

/-- **`StmtRel` depends only on what the symbolic state shows.** -/
theorem StmtRel.congr {ρ ρ' : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S S' : SymState}
    (h : StmtRel ρ E ctx rt S) (hash : ρ'.hash = solHash) (ok : ρ'.Ok) (facts : E.facts.Hold ρ')
    (frames : S.scopes.map (frameOfT ρ S.tags) = S'.scopes.map (frameOfT ρ' S'.tags))
    (store : ∀ k, k < wordSize → Writes.store ρ S.writes k = Writes.store ρ' S'.writes k)
    (logs : S.logs.map (Log.eval ρ) = S'.logs.map (Log.eval ρ'))
    (caller : S.caller.eval ρ = S'.caller.eval ρ' := by rfl)
    (hmem : ∀ id ws', S'.mem.lookup id = some ws' →
      ∃ ws, S.mem.lookup id = some ws ∧ memArr ρ ws = memArr ρ' ws' := by intro _ _ h; cases h)
    (hnext : ∀ k, S'.next = some k → S.next = some k := by intro _ h; cases h) :
    StmtRel ρ' E ctx rt S' :=
  { fields := h.fields
    events := h.events
    checked := h.checked
    sender := h.sender.trans caller
    hash := hash
    ok := ok
    frames := h.frames.trans frames
    store := fun k hk => (h.store k hk).trans (store k hk)
    logs := h.logs.trans logs
    facts := facts
    mem := fun id ws' hl => by
      obtain ⟨ws, h1, h2⟩ := hmem id ws' hl
      rw [← h2]
      exact h.mem id ws h1
    next := fun k hk => h.next k (hnext k hk) }

/-- The leaf of `x++` on a local word `x` whose word is `old`, `L'` the scopes with `x` set. -/
def incVarBr (old : WExpr) (L' : Scopes) (S : SymState) : Br :=
  guards (overflow .add old (.lit 1)).toList (.leaf (.normal { S with scopes := L' }))

theorem one_eq (ρ : Val) : (Value.word 1 : Value) = .word ((WExpr.lit 1).eval ρ) := rfl

theorem binOf_add : binOf .add = some .add := rfl

theorem pure_bind_sol {α β : Type} (a : α) (k : α → SolI β) : ((pure a : SolI α) >>= k) = k a := rfl

/-- `target++` on a target that resolves to `lv`, which holds the word `old`: `Panic(0x11)` when
`old` is the largest word, else `old + 1` written back, which leaves `rt'` related to `S'`. -/
theorem eval_inc (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) (post : Bool) {target : Expr} {lv : ResolvedLValue}
    {old : WExpr} {rt' : Runtime} {S' : SymState}
    (hres : ∀ F, target.orderFuel < F → Expr.resolveLValueFuel F ctx rt target = pure (lv, rt))
    (hread : ResolvedLValue.read ctx rt lv = .ok (.word (old.eval ρ)))
    (hwrite : ResolvedLValue.write ctx rt lv (.word ((WExpr.bin .add old (.lit 1)).eval ρ)) = .ok rt')
    (hrel' : StmtRel ρ E ctx rt' S') :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.incDec .add post (some (.uint 256)) target)) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((guards (overflow .add old (.lit 1)).toList (.leaf (.normal S'))).eval ρ) := by
  have happ := apply_erased ρ binOf_add old (.lit 1)
  rw [← one_eq] at happ
  have hcleq : ctx.checked = true := hrel.checked
  have hcl : ValueCleanup.apply true (.uint 256) (.word ((WExpr.bin .add old (.lit 1)).eval ρ)) =
      .ok (.word ((WExpr.bin .add old (.lit 1)).eval ρ)) := uintCleanup_256 _ (WExpr.eval_lt ρ _)
  rw [Stmt.eval]
  simp only [Expr.eval, Expr.orderFuel]
  rw [Expr.evalFuel, hres _ (by omega)]
  simp only [pure_bind_sol]
  rw [guards_eval]
  by_cases hg : (overflow .add old (.lit 1)).toList.any (fun g => g.eval ρ != 0) = true
  · have hE : ResolvedLValue.applyIncDecCleanup ctx rt lv .add post (.uint 256) =
        .error (.panic 0x11) := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, ↓reduceIte]
    rw [hE]
    simp only [hg, ↓reduceIte]
    exact ⟨.reverted rt (.panic 0x11), rfl, by simp only [failCode_overflow]; rfl⟩
  · have hE : ∃ v, ResolvedLValue.applyIncDecCleanup ctx rt lv .add post (.uint 256) =
        .ok (v, rt') := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, Bool.false_eq_true, ↓reduceIte,
        hcl, hwrite]
      cases post <;> exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := hE
    rw [hv]
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, hrel'⟩

/-- **`x++` on a local word.** -/
theorem eval_incVar (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) (post : Bool) {x : String} {old : WExpr} {L' : Scopes}
    (hold : S.word? x = some old)
    (hL : S.setW x (.bin .add old (.lit 1)) = some L') :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.incDec .add post (some (.uint 256)) (.var x))) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((incVarBr old L' S).eval ρ) := by
  have hx : rt.lookupLocal? x = some (.word (old.eval ρ)) := hrel.expr.locals x old hold
  have hbase : rt.lookupStorageBase? x = none := by simp [Runtime.lookupStorageBase?, hx]
  obtain ⟨hxw, hL0⟩ := SymState.setW_spec hL
  refine eval_inc ρ E ctx rt S hrel n post (lv := .local x) (rt' := { rt with locals := L'.map (frameOfT ρ S.tags) })
    (S' := { S with scopes := L' })
    (fun F hF => ?_) ?_ ?_ { hrel with frames := rfl }
  · obtain ⟨m, rfl⟩ : ∃ m, F = m + 1 := ⟨F - 1, by omega⟩
    simp only [Expr.resolveLValueFuel, hbase, hx]
  · simp [ResolvedLValue.read, ResolvedLValue.readRaw, hx, Runtime.derefMemoryValue, bind,
      Except.bind]
  · simp [ResolvedLValue.write, assignLocal_word hrel.frames hxw hL0]

/-- The leaf of `x++` on a word field of slot `k` at byte offset `off` of `bytes` bytes. -/
def incFieldBr (k off bytes : Nat) (S : SymState) : Br :=
  guards (overflow .add (readField (S.writes.read (.lit k)) off bytes) (.lit 1)).toList
    (.leaf (.normal { S with writes := (S.writes.set (.lit k)
      (writeField (S.writes.read (.lit k)) (.bin .add (readField (S.writes.read (.lit k)) off bytes)
        (.lit 1)) off bytes)) }))

/-- **`x++` on a word storage field.** -/
theorem eval_incField (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) (post : Bool) {x : String} {k off bytes : Nat}
    (hk : fieldOf? E.fields x = some (k, off, bytes)) :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.incDec .add post (some (.uint 256)) (.storageRead .header x []))) =
          .done (.ok r) ∧ LeafRel ρ E ctx r ((incFieldBr k off bytes S).eval ρ) := by
  obtain ⟨f, hfx, rfl, rfl, rfl⟩ := fieldOf?_spec hrel.fields hk
  have hsl : rt.state.loadSlot f.slot = (S.writes.read (.lit f.slot)).eval ρ :=
    slot_read hrel.expr hfx.slot
  have hslw : rt.state.loadSlot f.slot < wordSize := hsl ▸ WExpr.eval_lt _ _
  refine eval_inc ρ E ctx rt S hrel n post (lv := .storageField x) (fun F hF => ?_) ?_ ?_
    (hrel.writeField hfx _)
  · obtain ⟨m, rfl⟩ : ∃ m, F = m + 1 := ⟨F - 1, by omega⟩
    simp only [Expr.resolveLValueFuel]
  · simp [ResolvedLValue.read, ResolvedLValue.readRaw, load_field hfx hslw, hsl,
      Runtime.derefMemoryValue, bind, Except.bind, readField_eval ρ _ hfx.fits hfx.bytes]
  · simp only [ResolvedLValue.write, store_field hfx hslw _ (WExpr.eval_lt ρ _),
      writeField_eval ρ _ _ hfx.fits hfx.bytes, hsl]

/-- info: 'SolidCore.Refinement.Generic.Loop.eval_incField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_incField

/-- info: 'SolidCore.Refinement.Generic.Loop.eval_incVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_incVar

end SolidCore.Refinement.Generic.Loop

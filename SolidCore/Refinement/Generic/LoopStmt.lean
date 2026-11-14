import SolidCore.Refinement.Generic.Loop

/-!
# Increments of the loop fragment, and moving a relation between symbolic states

`i++` and `count++` on `uint256` words, the updates of most loops, as erasure leaves:
`eval_incVar` (a local word) and `eval_incField` (a word storage field) run SolidCore's
`Expr.incDec` statement under `StmtRel` to the leaf the overflow guard selects: `Panic(0x11)`
when the old word is `2 ^ 256 - 1`, else the old word plus one written back.

`StmtRel.congr` moves `StmtRel` to another valuation and symbolic state that show the same
locals, storage and logs: what a loop's invariant needs to name the state at its header with
fresh words for the values the loop changes.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source SolidCore.Refinement.Generic

/-- **`StmtRel` depends only on what the symbolic state shows.** -/
theorem StmtRel.congr {ρ ρ' : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S S' : SymState}
    (h : StmtRel ρ E ctx rt S) (hash : ρ'.hash = solHash) (ok : ρ'.Ok) (facts : E.facts.Hold ρ')
    (frames : S.scopes.map (frameOf ρ) = S'.scopes.map (frameOf ρ'))
    (store : ∀ k, k < wordSize → Writes.store ρ S.writes k = Writes.store ρ' S'.writes k)
    (logs : S.logs.map (Log.eval ρ) = S'.logs.map (Log.eval ρ')) :
    StmtRel ρ' E ctx rt S' :=
  { fields := h.fields
    events := h.events
    checked := h.checked
    sender := h.sender
    hash := hash
    ok := ok
    frames := h.frames.trans frames
    store := fun k hk => (h.store k hk).trans (store k hk)
    logs := h.logs.trans logs
    facts := facts }

/-- The leaf of `x++` on a local word `x` whose word is `old`, `L'` the scopes with `x` set. -/
def incVarBr (old : WExpr) (L' : Scopes) (S : SymState) : Br :=
  guards (overflow .add old (.lit 1)).toList (.leaf (.normal { S with scopes := L' }))

theorem one_eq (ρ : Val) : (Value.word 1 : Value) = .word ((WExpr.lit 1).eval ρ) := rfl

theorem binOf_add : binOf .add = some .add := rfl

theorem pure_bind_sol {α β : Type} (a : α) (k : α → SolI β) : ((pure a : SolI α) >>= k) = k a := rfl

set_option maxHeartbeats 2000000 in
/-- **`x++` on a local word.** -/
theorem eval_incVar (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) (post : Bool) {x : String} {old : WExpr} {L' : Scopes}
    (hold : Scopes.get? S.scopes x = some old)
    (hL : Scopes.set S.scopes x (.bin .add old (.lit 1)) = some L') :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.incDec .add post (some (.uint 256)) (.var x))) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((incVarBr old L' S).eval ρ) := by
  obtain ⟨old', hold'⟩ := Scopes.get?_of_set hL
  have hx : rt.lookupLocal? x = some (.word (old.eval ρ)) := hrel.expr.locals x old hold
  have hbase : rt.lookupStorageBase? x = none := by simp [Runtime.lookupStorageBase?, hx]
  have hassign : rt.assignLocal? x (.word ((WExpr.bin .add old (.lit 1)).eval ρ)) =
      some { rt with locals := L'.map (frameOf ρ) } := by
    simp [Runtime.assignLocal?, hx, Value.coerceLike?, hrel.frames, env_assign ρ S.scopes x _, hL]
  have hrel' : StmtRel ρ E ctx { rt with locals := L'.map (frameOf ρ) } { S with scopes := L' } :=
    { hrel with frames := rfl }
  have hread : ResolvedLValue.read ctx rt (.local x) = .ok (.word (old.eval ρ)) := by
    simp [ResolvedLValue.read, ResolvedLValue.readRaw, hx, Runtime.derefMemoryValue, bind,
      Except.bind]
  have hcl : ∀ w, w < wordSize → ValueCleanup.apply true (.uint 256) (.word w) = .ok (.word w) :=
    fun w hw => uintCleanup_256 w hw
  have happ := apply_erased ρ binOf_add old (.lit 1)
  rw [← one_eq] at happ
  have hcleq : ctx.checked = true := hrel.checked
  rw [Stmt.eval]
  simp only [Expr.eval, Expr.orderFuel]
  rw [Expr.evalFuel]
  simp only [Expr.resolveLValueFuel, hbase, hx, pure_bind_sol]
  unfold incVarBr
  rw [guards_eval]
  by_cases hg : (overflow .add old (.lit 1)).toList.any (fun g => g.eval ρ != 0) = true
  · have hE : ResolvedLValue.applyIncDecCleanup ctx rt (.local x) .add post (.uint 256) =
        .error (.panic 0x11) := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, ↓reduceIte]
    rw [hE]
    simp only [hg, ↓reduceIte]
    exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
  · have hE : ∃ v, ResolvedLValue.applyIncDecCleanup ctx rt (.local x) .add post (.uint 256) =
        .ok (v, { rt with locals := L'.map (frameOf ρ) }) := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, Bool.false_eq_true, ↓reduceIte, hcl _ (WExpr.eval_lt ρ _),
        ResolvedLValue.write, hassign]
      cases post <;> exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := hE
    rw [hv]
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, hrel'⟩

/-- The leaf of `x++` on a word field of slot `k` at byte offset `off` of `bytes` bytes. -/
def incFieldBr (k off bytes : Nat) (S : SymState) : Br :=
  guards (overflow .add (readField (S.writes.read (.lit k)) off bytes) (.lit 1)).toList
    (.leaf (.normal { S with writes := (S.writes.set (.lit k)
      (writeField (S.writes.read (.lit k)) (.bin .add (readField (S.writes.read (.lit k)) off bytes)
        (.lit 1)) off bytes)) }))

set_option maxHeartbeats 2000000 in
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
  have hst : ∀ w : WExpr, ResolvedLValue.write ctx rt (.storageField x) (.word (w.eval ρ)) =
      .ok { rt with state := (rt.state.storeSlot f.slot
        ((writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes).eval ρ)) } := by
    intro w
    simp only [ResolvedLValue.write, store_field hfx hslw _ (w.eval_lt ρ),
      writeField_eval ρ _ _ hfx.fits hfx.bytes, hsl]
  have hread : ResolvedLValue.read ctx rt (.storageField x) =
      .ok (.word ((readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes).eval ρ)) := by
    simp [ResolvedLValue.read, ResolvedLValue.readRaw, load_field hfx hslw, hsl,
      Runtime.derefMemoryValue, bind, Except.bind, readField_eval ρ _ hfx.fits hfx.bytes]
  have hcl : ∀ w, w < wordSize → ValueCleanup.apply true (.uint 256) (.word w) = .ok (.word w) :=
    fun w hw => uintCleanup_256 w hw
  have happ := apply_erased ρ binOf_add
    (readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes) (.lit 1)
  rw [← one_eq] at happ
  have hcleq : ctx.checked = true := hrel.checked
  rw [Stmt.eval]
  simp only [Expr.eval, Expr.orderFuel, Expr.listEvalFuel]
  rw [Expr.evalFuel]
  simp only [Expr.resolveLValueFuel, pure_bind_sol]
  unfold incFieldBr
  rw [guards_eval]
  by_cases hg : (overflow .add (readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes)
      (.lit 1)).toList.any (fun g => g.eval ρ != 0) = true
  · have hE : ResolvedLValue.applyIncDecCleanup ctx rt (.storageField x) .add post (.uint 256) =
        .error (.panic 0x11) := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, ↓reduceIte]
    rw [hE]
    simp only [hg, ↓reduceIte]
    exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
  · have hE : ∃ v, ResolvedLValue.applyIncDecCleanup ctx rt (.storageField x) .add post (.uint 256) =
        .ok (v, { rt with state := (rt.state.storeSlot f.slot
          ((writeField (S.writes.read (.lit f.slot)) (.bin .add (readField (S.writes.read (.lit f.slot))
            f.packedOffset f.packedBytes) (.lit 1)) f.packedOffset f.packedBytes).eval ρ)) }) := by
      simp only [ResolvedLValue.applyIncDecCleanup, hread, hcleq, bind, Except.bind,
        Value.oneLike?, happ, hg, Bool.false_eq_true, ↓reduceIte, hcl _ (WExpr.eval_lt ρ _), hst]
      cases post <;> exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := hE
    rw [hv]
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, hrel.writeField hfx _⟩

/-- info: 'SolidCore.Refinement.Generic.Loop.eval_incField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_incField

/-- info: 'SolidCore.Refinement.Generic.Loop.eval_incVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_incVar

end SolidCore.Refinement.Generic.Loop

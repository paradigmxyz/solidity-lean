import SolidCore.Refinement.Generic.Source
import SolidCore.Refinement.Generic.Event

/-!
# Statements of the fragment: erasure and simulation

`eraseStmt` erases a SolidCore statement of the fragment to a `Br`, a tree of branches on words
whose leaves say how the statement ends: normally with a new symbolic state, by returning words,
or by reverting (empty, or `Panic(code)`). `eval_stmt` proves that SolidCore's interpreter runs
the statement to the leaf the call's words select, with the runtime related to the leaf's
symbolic state by `StmtRel`: its locals scope by scope (`frameOf`), its storage as the writes
over the call's storage, and its logs.

The erasure reads the contract through an `EraseEnv`: its storage fields, its events and its
table of internal functions, which the relation asks to be the context's and the interpreter's.
-/

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity.Source

/-- Why a statement of the fragment reverts: with empty data, with `Panic(code)`, or with
`Error(msg)`, as `require(c, msg)` and `revert(msg)` do. -/
inductive Fail where
  | empty
  | panic (code : Nat)
  | error (msg : String)
  deriving DecidableEq, Repr

/-- SolidCore's revert data of a revert. -/
def Fail.data : Fail → RevertData
  | .empty => .empty
  | .panic c => .panic c
  | .error m => .error m

/-- The revert of a `require` or `revert` with the reason `r`, if any. -/
def failOf : Option String → Fail
  | none => .empty
  | some m => .error m

/-- How a statement of the fragment ends. -/
inductive Leaf where
  | normal (S : SymState)
  | returned (S : SymState) (vals : List WExpr)
  | reverted (f : Fail)
  deriving DecidableEq, Repr

/-- A statement's outcome as a tree of branches on words. -/
inductive Br where
  | leaf (l : Leaf)
  | ite (c : WExpr) (t e : Br)
  deriving DecidableEq, Repr

def Br.eval (ρ : Val) : Br → Leaf
  | .leaf l => l
  | .ite c t e => if c.eval ρ = 0 then e.eval ρ else t.eval ρ

/-- Revert with `Panic(0x11)` when one of the overflow conditions holds, else go on. -/
def guards (gs : List WExpr) (rest : Br) : Br :=
  gs.foldr (fun g acc => .ite g (.leaf (.reverted (.panic 0x11))) acc) rest

theorem guards_eval (ρ : Val) (gs : List WExpr) (rest : Br) :
    (guards gs rest).eval ρ =
      if gs.any (fun g => g.eval ρ != 0) then .reverted (.panic 0x11) else rest.eval ρ := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [guards, List.foldr_cons] at ih ⊢
    simp only [Br.eval, ih, List.any_cons]
    by_cases h : g.eval ρ = 0 <;> simp [h]

/-- A leaf with `f` applied to its state, if it has one. -/
def Leaf.mapS (f : SymState → SymState) : Leaf → Leaf
  | .normal S => .normal (f S)
  | .returned S vs => .returned (f S) vs
  | l => l

/-- Every leaf's state changed by `f`. -/
def Br.mapS (f : SymState → SymState) : Br → Br
  | .leaf l => .leaf (l.mapS f)
  | .ite c t e => .ite c (t.mapS f) (e.mapS f)

theorem Br.eval_mapS (ρ : Val) (f : SymState → SymState) : ∀ b : Br,
    (b.mapS f).eval ρ = (b.eval ρ).mapS f
  | .leaf _ => rfl
  | .ite c t e => by
    simp only [Br.mapS, Br.eval]
    split
    · exact Br.eval_mapS ρ f e
    · exact Br.eval_mapS ρ f t

/-- Run `k` on every leaf. -/
def Br.bindLeaf : Br → (Leaf → Option Br) → Option Br
  | .leaf l, k => k l
  | .ite c t e, k => do
    let t' ← t.bindLeaf k
    let e' ← e.bindLeaf k
    some (.ite c t' e')

theorem Br.bindLeaf_eval (ρ : Val) {k : Leaf → Option Br} : ∀ {b b' : Br}, b.bindLeaf k = some b' →
    ∃ c, k (b.eval ρ) = some c ∧ b'.eval ρ = c.eval ρ
  | .leaf l, b', h => ⟨b', h, rfl⟩
  | .ite c t e, b', h => by
    simp only [Br.bindLeaf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t', ht, e', he, rfl⟩ := h
    simp only [Br.eval]
    split
    · exact Br.bindLeaf_eval ρ he
    · exact Br.bindLeaf_eval ρ ht

/-- Run `k` on the state of every normal end. -/
def Br.bind : Br → (SymState → Option Br) → Option Br
  | .leaf (.normal S), k => k S
  | .leaf l, _ => some (.leaf l)
  | .ite c t e, k => do
    let t' ← t.bind k
    let e' ← e.bind k
    some (.ite c t' e')

/-- Assign the word `e` to the first local named `x`. -/
def Locals.set : Locals → String → WExpr → Option Locals
  | [], _, _ => none
  | (y, e') :: rest, x, e =>
    if y = x then some ((y, e) :: rest)
    else (Locals.set rest x e).map ((y, e') :: ·)

/-- Assign the word `e` to the local `x` of the innermost scope that has it. -/
def Scopes.set : Scopes → String → WExpr → Option Scopes
  | [], _, _ => none
  | L :: rest, x, e =>
    match L.set x e with
    | some L' => some (L' :: rest)
    | none => (Scopes.set rest x e).map (L :: ·)

/-- Declare the local `x` with the word `e` in the innermost scope. -/
def Scopes.declare : Scopes → String → WExpr → Scopes
  | [], x, e => [[(x, e)]]
  | L :: rest, x, e => ((x, e) :: L) :: rest

/-- The state with a new innermost scope, as a block enters. -/
def SymState.push (S : SymState) : SymState := { S with scopes := [] :: S.scopes }

/-- The state without its innermost scope, as a block leaves. -/
def SymState.pop (S : SymState) : SymState := { S with scopes := S.scopes.drop 1 }

/-- A type whose values the fragment holds as words: `uint256` and `address`. -/
def wordTy : Ty → Bool
  | .uint256 => true
  | .address => true
  | _ => false

theorem wordTy_coerce {ty : Ty} (h : wordTy ty = true) (v : Nat) :
    ty.coerceValue? (.word v) = some (.word v) ∧ ty.defaultValue = .word 0 := by
  cases ty <;> simp_all [wordTy, Ty.coerceValue?, Ty.defaultValue]

/-- What the erasure reads of the contract: its storage fields, its events and the table of its
internal functions, with the facts that hold of every call it erases (`facts`: the argument
checks of the external function, which bound its `address` words for logs). -/
structure EraseEnv where
  fields : List StorageField
  events : List EventDecl
  tbl : FunctionTable
  facts : Facts := []

/-- The erasure of a list of expressions: their overflow conditions and their words. -/
def eraseExprs (fields : List StorageField) (S : SymState) : List Expr → Option (List WExpr × List WExpr)
  | [] => some ([], [])
  | e :: es => do
    let (g, v) ← eraseExpr fields S e
    let (gs, vs) ← eraseExprs fields S es
    some (g ++ gs, v :: vs)

/-- A statement list, each statement erased by `f`. -/
def eraseSeq (f : Stmt → SymState → Option Br) : List Stmt → SymState → Option Br
  | [], S => some (.leaf (.normal S))
  | s :: rest, S => do
    let b ← f s S
    b.bind (eraseSeq f rest)

/-- The range check of a checked cleanup to `b` bits of the word `w`: none for `uint256`. -/
def cleanupGuard (b : Nat) (w : WExpr) : Option (List WExpr) :=
  if b = 256 then some []
  else if 0 < b ∧ b < 256 then some [.bin .gt w (.lit (2 ^ b - 1))]
  else none

/-- A binding the fragment holds as a word: a `uint256` or an `address`, not a storage
reference. -/
def wordDecl (b : BindingDecl) : Bool := wordTy b.ty && !b.isStorageRef

/-- An internal function's frame on entry: its parameters bound to the argument words, its
returns at zero. -/
def callFrame (fn : InternalFunction) (vs : List WExpr) : Locals :=
  (fn.params.zip vs).map (fun p => (p.1.name, p.2)) ++ fn.returns.map (fun r => (r.name, .lit 0))

/-- Assign words to locals, one after the other. -/
def Scopes.setMany : Scopes → List String → List WExpr → Option Scopes
  | sc, [], [] => some sc
  | sc, x :: xs, v :: vs => do
    let sc' ← Scopes.set sc x v
    Scopes.setMany sc' xs vs
  | _, _, _ => none

/-- The caller's state after an internal call returned the words `ws`: the call's targets
assigned, the callee's writes and logs. -/
def callAssign (targets : List String) (S S1 : SymState) (ws : List WExpr) : Option Br :=
  if targets = [] then some (.leaf (.normal { S with writes := S1.writes, logs := S1.logs }))
  else do
    let sc ← Scopes.setMany S.scopes targets ws
    some (.leaf (.normal { scopes := sc, writes := S1.writes, logs := S1.logs }))

/-- The end of an internal call from the end of its callee's body: its named returns or its
returned words assigned to the targets, or the callee's revert. -/
def callLeaf (fn : InternalFunction) (targets : List String) (S : SymState) : Leaf → Option Br
  | .normal S1 => do
    let ws ← fn.returns.mapM fun r => Scopes.get? S1.scopes r.name
    callAssign targets S S1 ws
  | .returned S1 vs =>
    if vs = [] then do
      let ws ← fn.returns.mapM fun r => Scopes.get? S1.scopes r.name
      callAssign targets S S1 ws
    else if vs.length = fn.returns.length then callAssign targets S S1 vs
    else none
  | .reverted p => some (.leaf (.reverted p))

/-- The end of a `captureReturn`: a return of words assigned to its names. -/
def captureLeaf (names : List String) : Leaf → Option Br
  | .returned S1 vs =>
    if vs = [] ∨ names = [] then some (.leaf (.normal S1))
    else do
      let sc ← Scopes.setMany S1.scopes names vs
      some (.leaf (.normal { S1 with scopes := sc }))
  | l => some (.leaf l)

/-- Which arguments of an event SolidCore takes as indexed, as `Stmt.emitEvent` computes it. -/
def emitFlags (decl? : Option EventDecl) (es : List Expr) : List Bool :=
  match decl? with
  | some decl =>
      if decl.fields.length == es.length then
        decl.fields.map (fun field => field.indexed)
      else if decl.fields.isEmpty then
        (List.range es.length).map (fun i => decide (i < decl.indexedCount))
      else
        List.replicate es.length false
  | none => List.replicate es.length false

/-- The order SolidCore evaluates an event's arguments in: the indexed ones last to first, then
the others first to last. -/
def emitSchedule (flags : List Bool) (n : Nat) : List Nat :=
  let positions := (List.range n).zip flags
  ((positions.filter (fun p => p.2)).reverse ++ positions.filter (fun p => !p.2)).map Prod.fst

/-- The values of an event's arguments in their positions, from the values in the order they
were evaluated in. -/
def unschedule {α : Type} (sched : List Nat) (vals : List α) (n : Nat) : List α :=
  (List.range n).filterMap (fun i => ((sched.zip vals).find? (fun p => p.1 == i)).map Prod.snd)

theorem unschedule_map {α β : Type} (f : α → β) (sched : List Nat) (vals : List α) (n : Nat) :
    unschedule sched (vals.map f) n = (unschedule sched vals n).map f := by
  simp only [unschedule, List.map_filterMap, List.zip_map_right, List.find?_map, Option.map_map]
  rfl

/-- The erasure of a statement of the fragment with fuel `n`, the fuel SolidCore runs it with:
skips, blocks (a scope each), assignments to locals and to storage fields, compound assignments
to storage fields (`v += x`, `w ^= x`: the operation's overflow check, then the cleanup's range
check), returns, `if` and panics. -/
def eraseStmt (E : EraseEnv) : Nat → Stmt → SymState → Option Br
  | 0, _, _ => none
  | n + 1, s, S =>
    match s with
    | .skip => some (.leaf (.normal S))
    | .block ss => do
      let b ← eraseSeq (eraseStmt E n) ss S.push
      some (b.mapS SymState.pop)
    | .assign (.var x) e => do
      let (gs, v) ← eraseExpr E.fields S e
      let L ← Scopes.set S.scopes x v
      some (guards gs (.leaf (.normal { S with scopes := L })))
    | .assign (.storage x) e => do
      let (k, off, bytes) ← fieldOf? E.fields x
      let (gs, v) ← eraseExpr E.fields S e
      some (guards gs (.leaf (.normal
        { S with writes := S.writes.set (.lit k) (writeField (S.writes.read (.lit k)) v off bytes) })))
    | .exprStmt (.assignment op? cleanup? (.storageRead .header x []) rhs) => do
      let (k, off, bytes) ← fieldOf? E.fields x
      let (gs, v) ← eraseExpr E.fields S rhs
      match op?, cleanup? with
      | none, none =>
        some (guards gs (.leaf (.normal
          { S with writes := S.writes.set (.lit k) (writeField (S.writes.read (.lit k)) v off bytes) })))
      | some op, some (.uint b) => do
        let o ← binOf op
        let w := WExpr.bin o (readField (S.writes.read (.lit k)) off bytes) v
        let cg ← cleanupGuard b w
        some (guards (gs ++ (overflow o (readField (S.writes.read (.lit k)) off bytes) v).toList ++ cg)
          (.leaf (.normal
            { S with writes := S.writes.set (.lit k) (writeField (S.writes.read (.lit k)) w off bytes) })))
      | _, _ => none
    | .exprStmt (.assignment (some op) (some (.uint b)) (.storageRead .element x [idx]) rhs) => do
      let k ← mapOf? E.fields x
      let (gs, v) ← eraseExpr E.fields S rhs
      let (gi, key) ← eraseExpr E.fields S idx
      let o ← binOf op
      let w := WExpr.bin o (S.writes.read (.hash key (.lit k))) v
      let cg ← cleanupGuard b w
      some (guards (gs ++ gi ++ (overflow o (S.writes.read (.hash key (.lit k))) v).toList ++ cg)
        (.leaf (.normal { S with writes := S.writes.set (.hash key (.lit k)) w })))
    | .varDecl ty x init =>
      if wordTy ty then
        match init with
        | none => some (.leaf (.normal { S with scopes := S.scopes.declare x (.lit 0) }))
        | some e => do
          let (gs, v) ← eraseExpr E.fields S e
          some (guards gs (.leaf (.normal { S with scopes := S.scopes.declare x v })))
      else none
    | .returnValues es => do
      let (gs, vs) ← eraseExprs E.fields S es
      some (guards gs (.leaf (.returned S vs)))
    | .ifElse c t e => do
      let (gs, v) ← eraseExpr E.fields S c
      let bt ← eraseStmt E n t S
      let be ← eraseStmt E n e S
      some (guards gs (.ite v bt be))
    | .panic code => some (.leaf (.reverted (.panic code)))
    | .requireStmt c r => do
      let (gs, v) ← eraseExpr E.fields S c
      some (guards gs (.ite v (.leaf (.normal S)) (.leaf (.reverted (failOf r)))))
    | .revertError r => some (.leaf (.reverted (failOf r)))
    | .assign (.storageIndex x i) e => do
      let (gs, v) ← eraseExpr E.fields S e
      let (gi, key) ← eraseExpr E.fields S i
      match mapOf? E.fields x with
      | some k =>
        some (guards (gs ++ gi) (.leaf (.normal { S with writes := S.writes.set (.hash key (.lit k)) v })))
      | none => do
        let k ← boolMapOf? E.fields x
        if bound E.facts v ≤ 1 then
          some (guards (gs ++ gi)
            (.leaf (.normal { S with writes := S.writes.set (.hash key (.lit k)) v })))
        else none
    | .assign (.index (.storageIndex x i1) i2) e => do
      let k ← map2Of? E.fields x
      let (gs, v) ← eraseExpr E.fields S e
      let (g1, k1) ← eraseExpr E.fields S i1
      let (g2, k2) ← eraseExpr E.fields S i2
      some (guards (gs ++ g1 ++ g2)
        (.leaf (.normal { S with writes := S.writes.set (.hash k2 (.hash k1 (.lit k))) v })))
    | .internalCall targets callee args => do
      let fn ← E.tbl.lookup? callee
      if fn.params.all wordDecl && fn.returns.all wordDecl && args.length = fn.params.length then
        let (gs, vs) ← eraseExprs E.fields S args
        let b ← eraseStmt E n fn.body { scopes := [callFrame fn vs], writes := S.writes, logs := S.logs }
        let b' ← b.bindLeaf (callLeaf fn targets S)
        some (guards gs b')
      else none
    | .captureReturn names body => do
      let b ← eraseStmt E n body S
      b.bindLeaf (captureLeaf names)
    | .emitEvent name es => do
      let decl ← E.events.find? (fun d => d.name == name)
      let t ← decl.topic?
      let sched := emitSchedule (emitFlags (some decl) es) es.length
      let (gs, svs) ← eraseExprs E.fields S (sched.filterMap (fun i => es[i]?))
      let ws := unschedule sched svs es.length
      if evOk E.facts decl.fields ws then
        some (guards gs (.leaf (.normal { S with logs := S.logs ++
          [⟨.lit t :: evTopics decl.fields ws, (evData decl.fields ws).flatMap wordOBytes⟩] })))
      else none
    | _ => none


/-! ## The relation between SolidCore's runtime and a symbolic state -/

/-- A scope of a function's locals, as SolidCore holds it. -/
def frameOf (ρ : Val) (L : Locals) : Frame := L.map fun p => (p.1, Value.word (p.2.eval ρ))

/-- What an event of SolidCore's state shows as a log: its topics and its data bytes. -/
def logOf (ev : Event) : List Nat × List Nat :=
  (ev.topics.map SolidCore.Solidity.Shared.norm,
    SolidCore.Solidity.Shared.Account.normalizeBytes ev.dataBytes)

/-- What SolidCore's runtime holds of a symbolic state inside a function body: the context's
storage fields and events are the erasure's, arithmetic is checked, the caller is `callerWord`,
the hash is SolidCore's, the locals are the state's scopes, every slot holds the word the writes
leave there, and the events are the state's logs. -/
structure StmtRel (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState) : Prop where
  fields : ctx.storageFields = E.fields
  events : ctx.eventDecls = E.events
  checked : ctx.checked = true
  sender : ctx.sender = callerWord
  hash : ρ.hash = solHash
  ok : ρ.Ok
  frames : rt.locals = S.scopes.map (frameOf ρ)
  store : ∀ k, k < wordSize → rt.state.loadSlot k = Writes.store ρ S.writes k
  logs : rt.state.events.map logOf = S.logs.map (Log.eval ρ)
  facts : E.facts.Hold ρ

theorem frame_lookup (ρ : Val) (L : Locals) (x : String) :
    Frame.lookup? (frameOf ρ L) x = (L.get? x).map fun e => Value.word (e.eval ρ) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨y, e⟩ := p
    simp only [frameOf, List.map_cons, Frame.lookup?, Locals.get?] at ih ⊢
    by_cases h : y = x <;> simp [h, ih]

theorem env_lookup (ρ : Val) : ∀ (sc : Scopes) (x : String),
    LocalEnv.lookup? (sc.map (frameOf ρ)) x = (Scopes.get? sc x).map fun e => Value.word (e.eval ρ)
  | [], _ => rfl
  | L :: rest, x => by
    simp only [List.map_cons, LocalEnv.lookup?, frame_lookup, Scopes.get?]
    cases L.get? x with
    | some e => rfl
    | none => exact env_lookup ρ rest x

theorem frame_assign (ρ : Val) (L : Locals) (x : String) (v : WExpr) :
    Frame.assign? (frameOf ρ L) x (Value.word (v.eval ρ)) = (L.set x v).map (frameOf ρ) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨y, e⟩ := p
    by_cases hy : y = x
    · subst hy; simp [frameOf, Frame.assign?, Locals.set]
    · simp only [frameOf, List.map_cons, Frame.assign?, Locals.set, hy, ↓reduceIte] at ih ⊢
      rw [ih]
      cases Locals.set L x v <;> rfl

theorem env_assign (ρ : Val) : ∀ (sc : Scopes) (x : String) (v : WExpr),
    LocalEnv.assign? (sc.map (frameOf ρ)) x (Value.word (v.eval ρ)) =
      (Scopes.set sc x v).map (·.map (frameOf ρ))
  | [], _, _ => rfl
  | L :: rest, x, v => by
    simp only [List.map_cons, LocalEnv.assign?, frame_assign, Scopes.set]
    cases L.set x v with
    | some L' => rfl
    | none =>
      simp only [Option.map_none, env_assign ρ rest x v]
      cases Scopes.set rest x v <;> rfl

theorem env_declare (ρ : Val) (sc : Scopes) (x : String) (v : WExpr) :
    LocalEnv.declare (sc.map (frameOf ρ)) x (Value.word (v.eval ρ)) =
      (sc.declare x v).map (frameOf ρ) := by
  cases sc <;> rfl

theorem Locals.get?_of_set {L L' : Locals} {x : String} {v : WExpr} (h : L.set x v = some L') :
    ∃ e, L.get? x = some e := by
  induction L generalizing L' with
  | nil => simp [Locals.set] at h
  | cons p L ih =>
    obtain ⟨y, e⟩ := p
    simp only [Locals.set] at h
    by_cases hy : y = x
    · exact ⟨e, by simp [Locals.get?, hy]⟩
    · simp only [hy, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨L'', h'', rfl⟩ := h
      obtain ⟨e', he'⟩ := ih h''
      exact ⟨e', by simp [Locals.get?, hy, he']⟩

theorem Scopes.get?_of_set : ∀ {sc sc' : Scopes} {x : String} {v : WExpr}, Scopes.set sc x v = some sc' →
    ∃ e, Scopes.get? sc x = some e
  | [], _, _, _, h => by simp [Scopes.set] at h
  | L :: rest, sc', x, v, h => by
    simp only [Scopes.set] at h
    cases hL : L.set x v with
    | some L' =>
      obtain ⟨e, he⟩ := Locals.get?_of_set hL
      exact ⟨e, by simp [Scopes.get?, he]⟩
    | none =>
      simp only [hL, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      obtain ⟨e, he⟩ := Scopes.get?_of_set hr
      have : L.get? x = none := by
        cases hg : L.get? x with
        | none => rfl
        | some e' =>
          exfalso
          clear hr he
          induction L with
          | nil => simp [Locals.get?] at hg
          | cons p L ih =>
            obtain ⟨y, e''⟩ := p
            simp only [Locals.get?, Locals.set] at hg hL
            by_cases hy : y = x
            · simp [hy] at hL
            · simp only [hy, ↓reduceIte, Option.map_eq_none_iff] at hg hL
              exact ih hL hg
      exact ⟨e, by simp [Scopes.get?, this, he]⟩

theorem StmtRel.expr {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (h : StmtRel ρ E ctx rt S) : ExprRel ρ E.fields ctx rt S where
  fields := h.fields
  checked := h.checked
  sender := h.sender
  hash := h.hash
  ok := h.ok
  locals x e he := by
    simp [Runtime.lookupLocal?, h.frames, env_lookup, he]
  store := h.store

theorem loadSlot_storeSlot (st : State) (k w q : Nat) (hk : k < wordSize) (hw : w < wordSize)
    (hq : q < wordSize) : (st.storeSlot k w).loadSlot q = if q = k then w else st.loadSlot q := by
  simp only [State.storeSlot, State.loadSlot, StorageMap.lookup?, StorageMap.insertLoop,
    norm_lt hk, norm_lt hw, norm_lt hq, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_iff_eq]
  by_cases h : q = k
  · simp [h]
  · have : ¬ k = q := fun e => h e.symm
    simp [h, this]

/-- Writing the word `v` to the slot `k` names keeps the relation, with the writes set. -/
theorem StmtRel.write {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) (k v : WExpr) :
    StmtRel ρ E ctx { rt with state := rt.state.storeSlot (k.eval ρ) (v.eval ρ) }
      { S with writes := S.writes.set k v } :=
  { fields := hrel.fields, events := hrel.events, checked := hrel.checked, sender := hrel.sender
    hash := hrel.hash, ok := hrel.ok, frames := hrel.frames
    store := fun q hq => by
      rw [loadSlot_storeSlot _ _ _ _ (k.eval_lt ρ) (v.eval_lt ρ) hq, Writes.store_set,
        hrel.store q hq, Nat.mod_eq_of_lt hq]
      by_cases h : q = k.eval ρ
      · simp [h]
      · simp [h, Ne.symm h]
    logs := by simp [State.storeSlot, hrel.logs]
    facts := hrel.facts }

/-- Writing a field keeps the relation, with the field's slot set to `writeField`. -/
theorem StmtRel.writeField {ρ : Val} {E : EraseEnv} {ctx : Context}
    {rt : Runtime} {S : SymState} (hrel : StmtRel ρ E ctx rt S) {x : String}
    {f : StorageField} (hfx : FieldOk ctx x f) (w : WExpr) :
    StmtRel ρ E ctx
      { rt with state := (rt.state.storeSlot f.slot
        ((writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes).eval ρ)) }
      { S with writes := (S.writes.set (.lit f.slot)
        (writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes)) } := by
  have h := hrel.write (.lit f.slot) (Generic.writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes)
  simp only [WExpr.eval, Nat.mod_eq_of_lt hfx.slot] at h
  exact h

/-! ## Simulation -/

/-- What SolidCore's result of a statement holds of the leaf it erases to. -/
def LeafRel (ρ : Val) (E : EraseEnv) (ctx : Context) : Result → Leaf → Prop
  | .normal rt, .normal S => StmtRel ρ E ctx rt S
  | .returned rt vs, .returned S ws =>
    StmtRel ρ E ctx rt S ∧ vs = ws.map fun e => Value.word (e.eval ρ)
  | .reverted _ r, .reverted f => r = f.data
  | _, _ => False

theorem caught_exprResult (ρ : Val) (gs : List WExpr) (v : WExpr) (rt : Runtime) :
    (exprResult ρ gs v rt).caught =
      .done (.ok (if gs.any (fun g => g.eval ρ != 0) then .error (.panic 0x11)
        else .ok (.word (v.eval ρ), rt))) := by
  unfold exprResult
  split <;> rfl

theorem eval_eq (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : ExprRel ρ fields ctx rt S) {e : Expr} {gs : List WExpr} {v : WExpr}
    (h : eraseExpr fields S e = some (gs, v)) : Expr.eval ctx rt e = exprResult ρ gs v rt :=
  eval_erase ρ fields ctx rt S hrel e gs v _ h (Nat.lt_succ_self _)

theorem Br.bind_eval (ρ : Val) {b b' : Br} {k : SymState → Option Br} (h : b.bind k = some b') :
    match b.eval ρ with
    | .normal S => ∃ c, k S = some c ∧ b'.eval ρ = c.eval ρ
    | l => b'.eval ρ = l := by
  induction b generalizing b' with
  | leaf l =>
    cases l with
    | normal S => exact ⟨b', h, rfl⟩
    | returned S vs => simp only [Br.bind, Option.some.injEq] at h; subst h; rfl
    | reverted p => simp only [Br.bind, Option.some.injEq] at h; subst h; rfl
  | ite c t e iht ihe =>
    simp only [Br.bind, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t', ht, e', he, rfl⟩ := h
    simp only [Br.eval]
    by_cases hc : c.eval ρ = 0
    · simp only [hc, ↓reduceIte]; exact ihe he
    · simp only [hc, ↓reduceIte]; exact iht ht

theorem eval_seq_of (ρ : Val) (E : EraseEnv) (ctx : Context) (n : Nat)
    (ih : ∀ s S b, eraseStmt E n s S = some b → ∀ rt, StmtRel ρ E ctx rt S →
      ∃ r, Stmt.eval n E.tbl ctx rt s = .done (.ok r) ∧ LeafRel ρ E ctx r (b.eval ρ)) :
    ∀ ss S b, eraseSeq (eraseStmt E n) ss S = some b → ∀ rt, StmtRel ρ E ctx rt S →
      ∃ r, Stmt.evalList n E.tbl ctx rt ss = .done (.ok r) ∧ LeafRel ρ E ctx r (b.eval ρ) := by
  intro ss
  induction ss with
  | nil =>
    intro S b h rt hrel
    simp only [eraseSeq, Option.some.injEq] at h
    subst h
    exact ⟨.normal rt, by rw [Stmt.evalList]; rfl, hrel⟩
  | cons s rest ihs =>
    intro S b h rt hrel
    simp only [eraseSeq, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b1, h1, hb⟩ := h
    obtain ⟨r1, hr1, hl1⟩ := ih s S b1 h1 rt hrel
    have hbe := Br.bind_eval ρ hb
    simp only [Stmt.evalList, hr1, bind, EvmCompiler.Simulation.Interaction.bind]
    revert hl1 hbe
    cases b1.eval ρ with
    | normal S1 =>
      intro hl1 hbe
      obtain ⟨c, hc, hce⟩ := hbe
      cases r1 <;> simp only [LeafRel] at hl1
      rename_i rt1
      obtain ⟨r, hr, hl⟩ := ihs S1 c hc rt1 hl1
      exact ⟨r, hr, hce ▸ hl⟩
    | returned S1 vs =>
      intro hl1 hbe
      cases r1 <;> simp only [LeafRel] at hl1
      exact ⟨_, rfl, hbe ▸ hl1⟩
    | reverted p =>
      intro hl1 hbe
      cases p <;> cases r1 <;> simp only [LeafRel] at hl1
      all_goals exact ⟨_, rfl, by rw [hbe]; exact hl1⟩

theorem StmtRel.popScope {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hr : StmtRel ρ E ctx rt S) : StmtRel ρ E ctx rt.popScope S.pop :=
  { hr with frames := by simp [Runtime.popScope, SymState.pop, hr.frames, List.map_drop] }

theorem LeafRel.popScope {ρ : Val} {E : EraseEnv} {ctx : Context}
    {r : Result} {l : Leaf} (h : LeafRel ρ E ctx r l) :
    LeafRel ρ E ctx (r.mapRuntime Runtime.popScope) (l.mapS SymState.pop) := by
  cases r <;> cases l <;> simp only [LeafRel, Result.mapRuntime, Leaf.mapS] at h ⊢
  · exact h.popScope
  · exact ⟨h.1.popScope, h.2⟩
  all_goals (rename_i p; cases p <;> simp_all [LeafRel])

theorem StmtRel.pushScope {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (h : StmtRel ρ E ctx rt S) : StmtRel ρ E ctx rt.pushScope S.push :=
  { h with frames := by simp [Runtime.pushScope, SymState.push, h.frames, frameOf] }

theorem caught_done_ok {α : Type} (a : α) :
    SolI.caught (EvmCompiler.Simulation.Interaction.done (.ok a) : SolI α) =
      EvmCompiler.Simulation.Interaction.done (.ok (.ok a)) := rfl

theorem bind_done_ok {α β : Type} (a : α) (k : α → SolI β) :
    ((EvmCompiler.Simulation.Interaction.done (.ok a) : SolI α) >>= k) = k a := rfl

theorem fieldWrite_lt {cur v off bytes : Nat} (hc : cur < wordSize) (hv : v < wordSize)
    (h : off + bytes ≤ 32) : fieldWrite cur v off bytes < wordSize := by
  unfold fieldWrite
  split
  · exact hv
  · exact replace_lt hc v _ _ (by omega)

theorem store_field {ctx : Context} {rt : Runtime} {x : String} {f : StorageField}
    (hf : FieldOk ctx x f) (hw : rt.state.loadSlot f.slot < wordSize) (v : Nat)
    (hv : v < wordSize) (sx : Bool) :
    rt.storeStorageFieldWithDeepClear ctx x (.word v) sx =
      .ok { rt with state := (rt.state.storeSlot f.slot
        (fieldWrite (rt.state.loadSlot f.slot) v f.packedOffset f.packedBytes)) } := by
  have := hf.bytes
  have := hf.fits
  simp [Runtime.storeStorageFieldWithDeepClear, hf.find, hf.layout, Runtime.storageMaterializedValue,
    Runtime.derefMemoryValueDeep, Runtime.derefMemoryValueWithFuel, Runtime.storeStorageField,
    coerceStorageWordAs, Value.forceAbiLazy, Ty.coerceValue?, Value.asStorageWord?, norm_lt hv,
    State.storeFieldWord, StorageField.isPacked, SolidCore.Solidity.Source.wordBytes,
    State.storeFieldSlot, hf.transient, bind, Except.bind, pure, Except.pure, State.loadFieldSlot,
    fieldWrite, wordReplaceBitRange, StorageField.packedBitWidth, StorageField.packedBitOffset,
    norm_lt hw]
  by_cases h : f.packedOffset = 0 ∧ f.packedBytes = 32
  · simp [h]
  · have hob8 : f.packedOffset * 8 + f.packedBytes * 8 ≤ 256 := by omega
    rw [if_pos (by omega), if_neg h, if_neg (by omega),
      replace_eq hw v _ _ hob8, norm_lt (replace_lt hw v _ _ hob8)]

/-- The overflow check of a checked binary operation of the fragment on two words. -/
theorem apply_erased (ρ : Val) {op : BinaryOp} {o : BinOp} (ho : binOf op = some o) (l r : WExpr) :
    BinaryOp.apply true op (.word (l.eval ρ)) (.word (r.eval ρ)) =
      if (overflow o l r).toList.any (fun g => g.eval ρ != 0) then .error (.panic 0x11)
      else .ok (.word ((WExpr.bin o l r).eval ρ)) := by
  have hl := l.eval_lt ρ
  have hr := r.eval_lt ρ
  cases op <;> simp only [binOf, reduceCtorEq, Option.some.injEq] at ho <;> subst ho
  · rw [apply_add _ _ hl hr]
    simp only [overflow, Option.toList_some, List.any_cons, List.any_nil, Bool.or_false, guard_add]
    by_cases h : wordSize ≤ l.eval ρ + r.eval ρ <;> simp [h, WExpr.eval, BinOp.eval, Nat.mod_mod]
  · rw [apply_sub _ _ hl hr]
    simp only [overflow, Option.toList_some, List.any_cons, List.any_nil, Bool.or_false, guard_sub]
    by_cases h : l.eval ρ < r.eval ρ <;> simp [h, WExpr.eval, BinOp.eval, Nat.mod_mod]
  · rw [apply_mul _ _ hl hr]
    simp only [overflow, Option.toList_some, List.any_cons, List.any_nil, Bool.or_false, guard_mul]
    by_cases h : wordSize ≤ l.eval ρ * r.eval ρ <;> simp [h, WExpr.eval, BinOp.eval, Nat.mod_mod]
  · rw [apply_bitAnd _ _ hl hr]
    simp [overflow, WExpr.eval, BinOp.eval, Nat.mod_mod]
  · rw [apply_bitOr _ _ hl hr]
    simp [overflow, WExpr.eval, BinOp.eval, Nat.mod_mod]
  · rw [apply_bitXor _ _ hl hr]
    simp [overflow, WExpr.eval, BinOp.eval, Nat.mod_mod]
  · rw [apply_lt _ _ hl hr]
    simp only [overflow, Option.toList_none, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    congr 2
    simp only [WExpr.eval, BinOp.eval]
    split <;> rfl
  · rw [apply_gt _ _ hl hr]
    simp only [overflow, Option.toList_none, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    congr 2
    simp only [WExpr.eval, BinOp.eval]
    split <;> rfl
  · rw [apply_eq _ _ hl hr]
    simp only [overflow, Option.toList_none, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    congr 2
    simp only [WExpr.eval, BinOp.eval]
    split <;> rfl

theorem cleanupGuard_spec (ρ : Val) {b : Nat} {w : WExpr} {cg : List WExpr}
    (h : cleanupGuard b w = some cg) :
    0 < b ∧ b ≤ 256 ∧ cg.any (fun g => g.eval ρ != 0) = !decide (w.eval ρ < 2 ^ b) := by
  have hw := w.eval_lt ρ
  unfold cleanupGuard at h
  split at h
  · rename_i hb
    subst hb
    simp only [Option.some.injEq] at h
    subst h
    simp [hw]
  · split at h
    · rename_i _ hb
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hb.1, by omega, ?_⟩
      have hpos := Nat.two_pow_pos b
      have hm : (2 ^ b - 1) % wordSize = 2 ^ b - 1 :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.sub_lt hpos (by decide))
          (Nat.pow_le_pow_right (by decide) (by omega)))
      by_cases hc : w.eval ρ < 2 ^ b
      · have : ¬ 2 ^ b - 1 < w.eval ρ := by omega
        simp [WExpr.eval, BinOp.eval, hm, this, hc]
      · have : 2 ^ b - 1 < w.eval ρ := by omega
        simp [WExpr.eval, BinOp.eval, hm, this, hc]
    · simp at h

theorem eval_returnList (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) :
    ∀ (es : List Expr) (gs vs : List WExpr) (fuel : Nat), eraseExprs fields S es = some (gs, vs) →
      es.length < fuel →
      Expr.evalReturnListFuel fuel ctx rt es =
        if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
        else .done (.ok (vs.map (fun e => Value.word (e.eval ρ)), rt)) := by
  intro es
  induction es with
  | nil =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [eraseExprs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Expr.evalReturnListFuel]
    rfl
  | cons e es ih =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [eraseExprs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨g, v⟩, he, ⟨gs', vs'⟩, hes, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hv : Expr.evalReturnValue ctx rt e = exprResult ρ g v rt := by
      have := eval_eq ρ fields ctx rt S hrel he
      unfold Expr.evalReturnValue
      split
      · rename_i x
        have hx : ∃ ex, Scopes.get? S.scopes x = some ex := by
          simp only [eraseExpr, Option.map_eq_some_iff] at he
          obtain ⟨ex, hex, -⟩ := he
          exact ⟨ex, hex⟩
        obtain ⟨ex, hex⟩ := hx
        have hmem : rt.lookupMemoryRef? x = none := by
          simp [Runtime.lookupMemoryRef?, hrel.locals x ex hex]
        simp only [hmem]
        exact this
      · exact this
    rw [Expr.evalReturnListFuel]
    simp only [hv, bind_exprResult, List.any_append]
    by_cases h1 : g.any (fun g => g.eval ρ != 0) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      rw [ih gs' vs' n hes (by simp at hf; omega)]
      by_cases h2 : gs'.any (fun g => g.eval ρ != 0) = true
      · simp [h2]; rfl
      · simp [h2]; rfl

theorem storeSlot_mod (st : State) (k w : Nat) : st.storeSlot (k % wordSize) w = st.storeSlot k w := by
  simp only [State.storeSlot, StorageMap.insertLoop, norm_mod, Nat.mod_mod]

/-- SolidCore writes the entry of a mapping at a key word to the slot `solHash key slot`. -/
theorem storeIndex_map {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {x : String} {k : Nat}
    (hk : mapOf? E.fields x = some k) {w v : Nat} (hw : w < wordSize) (hv : v < wordSize) :
    rt.storeStorageIndexWithDeepClear ctx x (.word w) (.word v) =
      .ok { rt with state := rt.state.storeSlot (solHash w k) v } := by
  obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk
  rcases hf.layout with hl | hl <;>
  simp [Runtime.storeStorageIndexWithDeepClear, hf.find, hl, mappingStorageSlotForKey,
    coerceMappingKeyWordAs, Value.forceAbiLazy, Ty.coerceValue?, Value.asStorageWord?, norm_lt hw,
    norm_lt hv, bind, Except.bind, State.storeStorageLayoutAtWithDeepClear,
    State.storeStorageLayoutAtWithDeepClearFuelMode, State.storeStorageLayoutAt, coerceStorageWordAs,
    Runtime.storageMaterializedValue, Runtime.derefMemoryValueDeep, Runtime.derefMemoryValueWithFuel,
    StorageLayout.clearDepth, mappingStorageSlot_eq, pure, Except.pure]

/-- A compound assignment to a mapping's entry, `m[i] op= rhs` with a `uint b` cleanup: the
right side's and the key's overflow conditions, the operation's, the cleanup's range check, then
the write of the entry's slot word. -/
theorem eval_mapAssign (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) {op : BinaryOp} {b : Nat} {x : String} {i rhs : Expr}
    {k : Nat} {gs gi : List WExpr} {v key : WExpr} {o : BinOp} {cg : List WExpr}
    (hk : mapOf? E.fields x = some k) (hv : eraseExpr E.fields S rhs = some (gs, v))
    (hi : eraseExpr E.fields S i = some (gi, key)) (ho : binOf op = some o)
    (hcg : cleanupGuard b (.bin o (S.writes.read (.hash key (.lit k))) v) = some cg) :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.assignment (some op) (some (.uint b)) (.storageRead .element x [i]) rhs)) =
        .done (.ok r) ∧
      LeafRel ρ E ctx r ((guards (gs ++ gi ++ (overflow o (S.writes.read (.hash key (.lit k))) v).toList ++ cg)
        (.leaf (.normal { S with writes := (S.writes.set (.hash key (.lit k))
          (.bin o (S.writes.read (.hash key (.lit k))) v)) }))).eval ρ) := by
  have hk' := hk
  obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk'
  have hread : (S.writes.read (.hash key (.lit f.slot))).eval ρ =
      Writes.store ρ S.writes (solHash (key.eval ρ) f.slot % wordSize) := by
    rw [Writes.eval_read hrel.ok]
    simp only [WExpr.eval, hrel.hash, Nat.mod_eq_of_lt hf.slot]
  rw [Stmt.eval]
  simp only [Expr.eval, Expr.orderFuel, Expr.listEvalFuel]
  rw [Expr.evalFuel]
  rw [eval_erase ρ E.fields ctx rt S hrel.expr rhs gs v _ hv (by omega)]
  rw [bind_exprResult]
  rw [guards_eval]
  have hrd : ResolvedLValue.read ctx rt (.storageIndex x (.word (key.eval ρ))) =
      .ok (.word ((S.writes.read (.hash key (.lit f.slot))).eval ρ)) := by
    simp [ResolvedLValue.read, ResolvedLValue.readRaw, loadIndex_map hrel.expr hk (key.eval_lt ρ),
      hread, Runtime.derefMemoryValue, bind, Except.bind]
  have hsl : (WExpr.hash key (.lit f.slot)).eval ρ = solHash (key.eval ρ) f.slot % wordSize := by
    simp only [WExpr.eval, hrel.hash, Nat.mod_eq_of_lt hf.slot]
  have hwr : ∀ w : WExpr, ResolvedLValue.write ctx rt (.storageIndex x (.word (key.eval ρ)))
      (.word (w.eval ρ)) =
        .ok { rt with state := (rt.state.storeSlot ((WExpr.hash key (.lit f.slot)).eval ρ) (w.eval ρ)) } := by
    intro w
    simp only [ResolvedLValue.write, storeIndex_map hrel hk (key.eval_lt ρ) (w.eval_lt ρ), hsl,
      storeSlot_mod]
  obtain ⟨hb0, hb, hcgv⟩ := cleanupGuard_spec ρ hcg
  have hcl : ∀ w : WExpr, ValueCleanup.apply true (.uint b) (.word (w.eval ρ)) =
      if w.eval ρ < 2 ^ b then .ok (.word (w.eval ρ)) else .error (.panic 0x11) :=
    fun w => uintCleanup_lt _ _ (w.eval_lt ρ) hb0 hb
  simp only [any_append]
  by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
  · simp only [hg, ↓reduceIte, Bool.true_or]
    exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
  · simp only [hg, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    rw [Expr.resolveLValueFuel]
    simp only []
    rw [eval_erase ρ E.fields ctx rt S hrel.expr i gi key _ hi (by omega), bind_exprResult]
    by_cases hgi : gi.any (fun g => g.eval ρ != 0) = true
    · simp only [hgi, ↓reduceIte, Bool.true_or]
      exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
    · simp only [hgi, Bool.false_eq_true, ↓reduceIte, Bool.false_or, bind_done_ok, pure,
        EvmCompiler.Simulation.Interaction.pure, liftM, monadLift, MonadLift.monadLift,
        SolI.ofExcept, hrd, hrel.checked, apply_erased ρ ho, hcgv]
      by_cases ho' : (overflow o (S.writes.read (.hash key (.lit f.slot))) v).toList.any
          (fun g => g.eval ρ != 0) = true
      · simp only [ho', Bool.true_or, ↓reduceIte]
        exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
      · simp only [ho', Bool.false_or, Bool.false_eq_true, ↓reduceIte, bind_done_ok]
        have hcl' := hcl (.bin o (S.writes.read (.hash key (.lit f.slot))) v)
        cases op
        all_goals first | (simp [binOf] at ho; done) | skip
        all_goals
        dsimp only
        rw [hcl']
        by_cases hc : (WExpr.bin o (S.writes.read (.hash key (.lit f.slot))) v).eval ρ < 2 ^ b
        · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            bind_done_ok, hwr]
          exact ⟨_, rfl, hrel.write _ _⟩
        · simp only [hc, decide_false, Bool.not_false, ↓reduceIte]
          exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩


/-- A plain write of a `bool` word to a mapping to `bool`'s entry stores the word in the entry's
slot. -/
theorem storeIndex_boolMap {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {x : String} {k : Nat}
    (hk : boolMapOf? E.fields x = some k) {w v : Nat} (hw : w < wordSize) (hv : v ≤ 1) :
    rt.storeStorageIndexWithDeepClear ctx x (.word w) (.word v) =
      .ok { rt with state := rt.state.storeSlot (solHash w k) v } := by
  obtain ⟨f, hf, rfl⟩ := boolMapOf?_spec hrel.fields hk
  have hv' : v = 0 ∨ v = 1 := by omega
  rcases hf.layout with hl | hl <;> rcases hv' with rfl | rfl <;>
  simp [Runtime.storeStorageIndexWithDeepClear, hf.find, hl, mappingStorageSlotForKey,
    coerceMappingKeyWordAs, Value.forceAbiLazy, Ty.coerceValue?, Value.asStorageWord?, norm_lt hw,
    bind, Except.bind, State.storeStorageLayoutAtWithDeepClear,
    State.storeStorageLayoutAtWithDeepClearFuelMode, State.storeStorageLayoutAt, coerceStorageWordAs,
    Runtime.storageMaterializedValue, Runtime.derefMemoryValueDeep, Runtime.derefMemoryValueWithFuel,
    StorageLayout.clearDepth, mappingStorageSlot_eq, pure, Except.pure, wordEq,
    SolidCore.Solidity.Shared.norm, modulus_eq, Nat.mod_eq_of_lt hw]

/-- A plain write of a word to a nested mapping's entry stores the word in the entry's slot. -/
theorem storePath_map2 {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {x : String} {k : Nat}
    (hk : map2Of? E.fields x = some k) {w1 w2 v : Nat} (h1 : w1 < wordSize) (h2 : w2 < wordSize)
    (hv : v < wordSize) :
    rt.storeStoragePathWithDeepClear ctx x [.word w1, .word w2] (.word v) =
      .ok { rt with state := rt.state.storeSlot (solHash w2 (solHash w1 k)) v } := by
  obtain ⟨f, hf, rfl⟩ := map2Of?_spec hrel.fields hk
  rw [Runtime.storeStoragePathWithDeepClear, Runtime.storeStorageBasePathWithDeepClear]
  simp only [Runtime.storageMaterializedValue, Runtime.derefMemoryValueDeep,
    Runtime.derefMemoryValueWithFuel, bind, Except.bind, pure, Except.pure]
  rw [resolve_map2 hf h1 h2]
  simp [State.storeStorageLayoutAtWithDeepClear, State.storeStorageLayoutAtWithDeepClearFuelMode,
    State.storeStorageLayoutAt, coerceStorageWordAs, Value.forceAbiLazy, Ty.coerceValue?,
    Value.asStorageWord?, norm_lt hv, StorageLayout.clearDepth, bind, Except.bind, pure, Except.pure]

/-- SolidCore resolves the target `m[i]` to the entry at `i`'s word, after `i`'s overflow
checks. -/
theorem resolve_storageIndex (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) (x : String) {i : Expr} {gi : List WExpr}
    {key : WExpr} (hi : eraseExpr fields S i = some (gi, key)) :
    (LValue.resolveWithRuntime (.storageIndex x i) ctx rt).caught =
      .done (.ok (if gi.any (fun g => g.eval ρ != 0) then .error (.panic 0x11)
        else .ok (.storageIndex x (.word (key.eval ρ)), rt))) := by
  simp only [LValue.resolveWithRuntime, Expr.resolveLValue, LValue.toExpr, Expr.storageIndex,
    Expr.orderFuel, Expr.listEvalFuel]
  rw [Expr.resolveLValueFuel]
  rw [eval_erase ρ fields ctx rt S hrel i gi key _ hi (by omega)]
  unfold exprResult
  split <;> rfl

/-- SolidCore resolves the target `m[i1][i2]` to the path of the two keys' words, after their
overflow checks. -/
theorem resolve_index2 (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) (x : String) {i1 i2 : Expr}
    {g1 g2 : List WExpr} {k1 k2 : WExpr} (h1 : eraseExpr fields S i1 = some (g1, k1))
    (h2 : eraseExpr fields S i2 = some (g2, k2)) :
    (LValue.resolveWithRuntime (.index (.storageIndex x i1) i2) ctx rt).caught =
      .done (.ok (if (g1 ++ g2).any (fun g => g.eval ρ != 0) then .error (.panic 0x11)
        else .ok (.storagePath x [.word (k1.eval ρ), .word (k2.eval ρ)], rt))) := by
  simp only [LValue.resolveWithRuntime, Expr.resolveLValue, LValue.toExpr, Expr.storageIndex,
    Expr.orderFuel, Expr.listEvalFuel]
  rw [Expr.resolveLValueFuel]
  rw [Expr.resolveLValueFuel]
  rw [eval_erase ρ fields ctx rt S hrel i1 g1 k1 _ h1 (by omega), bind_exprResult]
  by_cases hg1 : g1.any (fun g => g.eval ρ != 0) = true
  · simp only [hg1, any_append, Bool.true_or, ↓reduceIte]
    rfl
  · simp only [hg1, Bool.false_eq_true, ↓reduceIte, bind_done_ok, pure,
      EvmCompiler.Simulation.Interaction.pure]
    rw [eval_erase ρ fields ctx rt S hrel i2 g2 k2 _ h2 (by omega), bind_exprResult]
    by_cases hg2 : g2.any (fun g => g.eval ρ != 0) = true
    · simp only [hg2, any_append, Bool.or_true, ↓reduceIte]
      rfl
    · simp only [hg2, any_append, hg1, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      rfl

theorem eval_exprList (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) :
    ∀ (es : List Expr) (gs vs : List WExpr) (fuel : Nat), eraseExprs fields S es = some (gs, vs) →
      Expr.listEvalFuel es ≤ fuel →
      Expr.evalListFuel fuel ctx rt es =
        if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
        else .done (.ok (vs.map (fun e => Value.word (e.eval ρ)), rt)) := by
  intro es
  induction es with
  | nil =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [Expr.listEvalFuel] at hf; omega⟩
    simp only [eraseExprs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Expr.evalListFuel]
    rfl
  | cons e es ih =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [Expr.listEvalFuel] at hf; omega⟩
    simp only [eraseExprs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨g, v⟩, he, ⟨gs', vs'⟩, hes, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.listEvalFuel] at hf
    have hpos : 1 ≤ Expr.listEvalFuel es := by cases es <;> simp [Expr.listEvalFuel]
    rw [Expr.evalListFuel]
    simp only [eval_erase ρ fields ctx rt S hrel e g v n he (by omega), bind_exprResult,
      List.any_append]
    by_cases h1 : g.any (fun g => g.eval ρ != 0) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      rw [ih gs' vs' n hes (by omega)]
      by_cases h2 : gs'.any (fun g => g.eval ρ != 0) = true
      · simp [h2]; rfl
      · simp [h2]; rfl

theorem materialize_words (ctx : Context) (rt : Runtime) (ρ : Val) : ∀ ws : List WExpr,
    rt.materializeForValueUseList ctx (ws.map fun e => Value.word (e.eval ρ)) =
      .ok (ws.map fun e => Value.word (e.eval ρ))
  | [] => rfl
  | w :: ws => by
    simp [Runtime.materializeForValueUseList, Runtime.materializeForValueUse,
      Runtime.materializeForValueUseFuel, materialize_words ctx rt ρ ws, bind, Except.bind, pure,
      Except.pure]

/-- SolidCore emits a log of the fragment as the log the erasure appends. -/
theorem emit_words (ρ : Val) (ctx : Context) (rt : Runtime) {name : String} {decl : EventDecl}
    {t : Nat} (hfind : ctx.eventDecl? name = some decl) (ht : decl.topic? = some t)
    {K : Facts} (hK : K.Hold ρ) {ws : List WExpr} (hok : evOk K decl.fields ws = true) :
    ∃ ev rt', rt.emitEvent ctx name (ws.map fun e => Value.word (e.eval ρ)) = .ok rt' ∧
      rt'.state.events = rt.state.events ++ [ev] ∧ rt'.locals = rt.locals ∧
      rt'.state.storage = rt.state.storage ∧
      logOf ev = Log.eval ρ ⟨.lit t :: evTopics decl.fields ws, (evData decl.fields ws).flatMap wordOBytes⟩ := by
  obtain ⟨a, b, henc⟩ := encode_ok ρ hK decl.fields ws hok
  have hdata := encodeValues_ok ρ hK decl.fields ws hok
  have hun : (ws.map fun e => Value.word (e.eval ρ)).map Value.untagFixedBytes =
      ws.map fun e => Value.word (e.eval ρ) := by
    simp [Value.untagFixedBytes]
  simp only [Runtime.emitEvent, hun, hfind, ht, Option.isNone_some, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, EventDecl.encodeFields?, henc, hdata,
    SolidCore.Solidity.Shared.Log.append]
  refine ⟨?ev, ?rt', ?h0, ?ha, ?hb, ?hc, ?hd⟩
  case h0 => exact rfl
  case ha => exact rfl
  case hb => first | exact rfl | trivial
  case hc => first | exact rfl | trivial
  simp only [logOf, Log.eval, Option.toList_some, List.cons_append, List.nil_append, List.map_cons,
    WExpr.eval, norm_mod, List.map_map]
  refine Prod.ext ?_ ?_
  · simp only [List.cons.injEq]
    refine ⟨by first | rfl | trivial, ?_⟩
    apply List.map_congr_left
    intro e _
    simp [norm_mod, Nat.mod_eq_of_lt (e.eval_lt ρ)]
  · simp only [SolidCore.Solidity.Shared.Account.normalizeBytes, List.map_map]
    apply List.map_congr_left
    intro b _
    simp only [Function.comp, SolidCore.Solidity.Shared.Account.byte]
    cases b <;> simp [OByte.eval, Nat.mod_mod]

theorem eraseExprs_length {fields : List StorageField} {S : SymState} :
    ∀ {es : List Expr} {gs vs : List WExpr}, eraseExprs fields S es = some (gs, vs) →
      vs.length = es.length
  | [], gs, vs, h => by
    simp only [eraseExprs, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; rfl
  | e :: es, gs, vs, h => by
    simp only [eraseExprs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨g, v⟩, -, ⟨gs', vs'⟩, hes, h⟩ := h
    simp only [Prod.mk.injEq] at h
    rw [← h.2, List.length_cons, List.length_cons, eraseExprs_length hes]

theorem assignLocal_word {ρ : Val} {rt : Runtime} {sc sc' : Scopes} {x : String} {v : WExpr}
    (hfr : rt.locals = sc.map (frameOf ρ)) (h : Scopes.set sc x v = some sc') :
    rt.assignLocal? x (.word (v.eval ρ)) = some { rt with locals := sc'.map (frameOf ρ) } := by
  obtain ⟨old, hold⟩ := Scopes.get?_of_set h
  have hx : rt.lookupLocal? x = some (.word (old.eval ρ)) := by
    simp [Runtime.lookupLocal?, hfr, env_lookup, hold]
  simp [Runtime.assignLocal?, hx, Value.coerceLike?, hfr, env_assign ρ sc x v, h]

theorem assignMany_words {ρ : Val} : ∀ (xs : List String) (ws : List WExpr) (rt : Runtime)
    (sc sc' : Scopes), rt.locals = sc.map (frameOf ρ) → Scopes.setMany sc xs ws = some sc' →
    rt.assignNamedValues? xs (ws.map fun e => .word (e.eval ρ)) =
        some { rt with locals := sc'.map (frameOf ρ) } ∧
      rt.assignNamedValuesRef? xs (ws.map fun e => .word (e.eval ρ)) =
        some { rt with locals := sc'.map (frameOf ρ) }
  | [], [], rt, sc, sc', hfr, h => by
    simp only [Scopes.setMany, Option.some.injEq] at h
    subst h
    rw [← hfr]
    exact ⟨rfl, rfl⟩
  | x :: xs, w :: ws, rt, sc, sc', hfr, h => by
    simp only [Scopes.setMany, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨sc1, h1, h2⟩ := h
    have ha := assignLocal_word hfr h1
    obtain ⟨ih1, ih2⟩ := assignMany_words xs ws { rt with locals := sc1.map (frameOf ρ) } sc1 sc' rfl h2
    simp only [List.map_cons, Runtime.assignNamedValues?, Runtime.assignNamedValuesRef?,
      Runtime.assignLocalRefAware?, ha]
    exact ⟨ih1, ih2⟩
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => by simp [Scopes.setMany] at h

theorem eval_refArgs (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) :
    ∀ (es : List Expr) (gs vs : List WExpr) (fuel : Nat), eraseExprs fields S es = some (gs, vs) →
      Expr.listEvalFuel es ≤ fuel →
      Expr.evalRefArgListFuel fuel ctx rt es =
        if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
        else .done (.ok (vs.map (fun e => Value.word (e.eval ρ)), rt)) := by
  intro es
  induction es with
  | nil =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [Expr.listEvalFuel] at hf; omega⟩
    simp only [eraseExprs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Expr.evalRefArgListFuel]
    rfl
  | cons e es ih =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [Expr.listEvalFuel] at hf; omega⟩
    simp only [eraseExprs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨g, v⟩, he, ⟨gs', vs'⟩, hes, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.listEvalFuel] at hf
    have hpos : 1 ≤ Expr.listEvalFuel es := by cases es <;> simp [Expr.listEvalFuel]
    have hv : Expr.evalRefArg ctx rt e = exprResult ρ g v rt := by
      have := eval_eq ρ fields ctx rt S hrel he
      unfold Expr.evalRefArg
      split
      · rename_i x
        have hx : ∃ ex, Scopes.get? S.scopes x = some ex := by
          simp only [eraseExpr, Option.map_eq_some_iff] at he
          obtain ⟨ex, hex, -⟩ := he
          exact ⟨ex, hex⟩
        obtain ⟨ex, hex⟩ := hx
        have hl := hrel.locals x ex hex
        have hb : rt.lookupStorageBase? x = none := by simp [Runtime.lookupStorageBase?, hl]
        have hm : rt.lookupMemoryRef? x = none := by simp [Runtime.lookupMemoryRef?, hl]
        simp only [hb, hm]
        exact this
      · exact this
    rw [Expr.evalRefArgListFuel]
    simp only [hv, bind_exprResult, List.any_append]
    by_cases h1 : g.any (fun g => g.eval ρ != 0) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      rw [ih gs' vs' n hes (by omega)]
      by_cases h2 : gs'.any (fun g => g.eval ρ != 0) = true
      · simp [h2]; rfl
      · simp [h2]; rfl

theorem wordDecl_spec {b : BindingDecl} (h : wordDecl b = true) (v : Nat) :
    b.ty.coerceValue? (.word v) = some (.word v) ∧ b.defaultBinding = (b.name, .word 0) := by
  simp only [wordDecl, Bool.and_eq_true, Bool.not_eq_true'] at h
  have := wordTy_coerce h.1 v
  refine ⟨this.1, ?_⟩
  simp [BindingDecl.defaultBinding, h.2, (wordTy_coerce h.1 0).2]

theorem bindArgsRef_words (ρ : Val) : ∀ (ps : List BindingDecl) (vs : List WExpr),
    ps.all wordDecl = true → vs.length = ps.length →
    BindingDecl.bindArgsRef? ps (vs.map fun e => .word (e.eval ρ)) =
      some ((ps.zip vs).map fun p => (p.1.name, Value.word (p.2.eval ρ)))
  | [], [], _, _ => rfl
  | p :: ps, v :: vs, hp, hl => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    have ih := bindArgsRef_words ρ ps vs hp.2 (by simpa using hl)
    simp [BindingDecl.bindArgsRef?, BindingDecl.bindArgRef?, BindingDecl.bindArg?,
      (wordDecl_spec hp.1 _).1, ih, bind, Option.bind]
  | [], _ :: _, _, hl | _ :: _, [], _, hl => by simp at hl

theorem initialFrame_words (ρ : Val) (fn : InternalFunction) (vs : List WExpr)
    (hp : fn.params.all wordDecl = true) (hr : fn.returns.all wordDecl = true)
    (hl : vs.length = fn.params.length) :
    fn.initialFrame? (vs.map fun e => .word (e.eval ρ)) = some (frameOf ρ (callFrame fn vs)) := by
  have hd : fn.returnDefaultBindings = fn.returns.map fun r => (r.name, Value.word 0) := by
    simp only [InternalFunction.returnDefaultBindings]
    apply List.map_congr_left
    intro r hrm
    exact (wordDecl_spec (List.all_eq_true.mp hr r hrm) 0).2
  simp only [InternalFunction.initialFrame?, bindArgsRef_words ρ fn.params vs hp hl, hd, callFrame,
    frameOf, List.map_append, List.map_map]
  rfl

theorem deref_word' (rt : Runtime) (v : Nat) : rt.derefMemoryValueDeep (.word v) = .ok (.word v) := by
  simp [Runtime.derefMemoryValueDeep, Runtime.derefMemoryValueWithFuel]

theorem collectRef_words (ρ : Val) (rt : Runtime) (sc : Scopes)
    (hfr : rt.locals = sc.map (frameOf ρ)) : ∀ (rs : List BindingDecl) (ws : List WExpr),
    rs.all wordDecl = true → rs.mapM (fun r => Scopes.get? sc r.name) = some ws →
    collectReturnBindingsRef.collect rt rs = .ok (ws.map fun e => .word (e.eval ρ))
  | [], ws, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | r :: rs, ws, hr, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hr
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    have hl : rt.lookupLocal? r.name = some (.word (w.eval ρ)) := by
      simp [Runtime.lookupLocal?, hfr, env_lookup, hw]
    simp [collectReturnBindingsRef.collect, hl, deref_word', (wordDecl_spec hr.1 _).1,
      collectRef_words ρ rt sc hfr rs ws' hr.2 hws', bind, Except.bind, pure, Except.pure]

theorem coerceRef_words (ρ : Val) (rt : Runtime) : ∀ (rs : List BindingDecl) (vs : List WExpr),
    rs.all wordDecl = true → vs.length = rs.length →
    coerceReturnBindingsRef.coerce rt rs (vs.map fun e => .word (e.eval ρ)) =
      .ok (vs.map fun e => .word (e.eval ρ))
  | [], [], _, _ => rfl
  | r :: rs, v :: vs, hr, hl => by
    simp only [List.all_cons, Bool.and_eq_true] at hr
    simp [coerceReturnBindingsRef.coerce, deref_word', (wordDecl_spec hr.1 _).1,
      coerceRef_words ρ rt rs vs hr.2 (by simpa using hl), bind, Except.bind, pure, Except.pure]
  | [], _ :: _, _, hl | _ :: _, [], _, hl => by simp at hl

theorem callAssign_ok {ρ : Val} {E : EraseEnv} {ctx : Context} {rt rt1 : Runtime} {S S1 : SymState}
    (hrel : StmtRel ρ E ctx rt S) (hrel1 : StmtRel ρ E ctx rt1 S1) {targets : List String}
    {ws : List WExpr} {c : Br} (h : callAssign targets S S1 ws = some c) :
    ∃ r, internalCallAssign { rt1 with locals := rt.locals } targets
        (ws.map fun e => .word (e.eval ρ)) = .done (.ok r) ∧ LeafRel ρ E ctx r (c.eval ρ) := by
  unfold callAssign at h
  split at h
  · rename_i ht
    subst ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, { hrel1 with frames := hrel.frames }⟩
  · rename_i ht
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨sc, hsc, rfl⟩ := h
    have := (assignMany_words targets ws { rt1 with locals := rt.locals } S.scopes sc hrel.frames hsc).2
    have hne : targets.isEmpty = false := by cases targets <;> simp_all
    refine ⟨.normal { rt1 with locals := sc.map (frameOf ρ) }, ?_,
      (show StmtRel ρ E ctx { rt1 with locals := sc.map (frameOf ρ) }
        { scopes := sc, writes := S1.writes, logs := S1.logs } from { hrel1 with frames := rfl })⟩
    simp only [internalCallAssign, hne, Bool.false_eq_true, ↓reduceIte, this]
    rfl

theorem finish_call {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {fn : InternalFunction} {targets : List String}
    (hr : fn.returns.all wordDecl = true) :
    ∀ (rc : Result) (l : Leaf) (c : Br), LeafRel ρ E ctx rc l → callLeaf fn targets S l = some c →
      ∃ r, internalCallFinish fn targets rt.locals rc = .done (.ok r) ∧ LeafRel ρ E ctx r (c.eval ρ)
  | .normal rt1, .normal S1, c, h1, h => by
    simp only [LeafRel] at h1
    simp only [callLeaf, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ws, hws, h⟩ := h
    simp only [internalCallFinish, collectReturnBindingsRef,
      collectRef_words ρ rt1 S1.scopes h1.frames fn.returns ws hr hws]
    exact callAssign_ok hrel h1 h
  | .returned rt1 vals, .returned S1 vs, c, h1, h => by
    simp only [LeafRel] at h1
    obtain ⟨h1, rfl⟩ := h1
    simp only [callLeaf] at h
    split at h
    · rename_i hv
      subst hv
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ws, hws, h⟩ := h
      simp only [internalCallFinish, List.map_nil, List.isEmpty_nil, ↓reduceIte, collectReturnBindingsRef,
        collectRef_words ρ rt1 S1.scopes h1.frames fn.returns ws hr hws]
      exact callAssign_ok hrel h1 h
    · rename_i hv
      split at h
      · rename_i hl
        have hne : (vs.map fun e => Value.word (e.eval ρ)).isEmpty = false := by
          cases vs with
          | nil => exact absurd rfl hv
          | cons _ _ => rfl
        simp only [internalCallFinish, hne, Bool.false_eq_true, ↓reduceIte, coerceReturnBindingsRef,
          coerceRef_words ρ rt1 fn.returns vs hr hl]
        exact callAssign_ok hrel h1 h
      · simp at h
  | .reverted rt1 err, .reverted p, c, h1, h => by
    simp only [callLeaf, Option.some.injEq] at h
    subst h
    exact ⟨.reverted rt1 err, rfl, h1⟩
  | .normal _, .returned _ _, _, h1, _ | .normal _, .reverted _, _, h1, _
  | .returned _ _, .normal _, _, h1, _ | .returned _ _, .reverted _, _, h1, _
  | .reverted _ _, .normal _, _, h1, _ | .reverted _ _, .returned _ _, _, h1, _
  | .broke _, _, _, h1, _ | .continued _, _, _, h1, _ | .selfdestructed _, _, _, h1, _ => by
    first | (cases h1) | (rename_i l; cases l <;> cases h1) | skip

theorem capture_ok {ρ : Val} {E : EraseEnv} {ctx : Context} (names : List String) :
    ∀ (rc : Result) (l : Leaf) (c : Br), LeafRel ρ E ctx rc l → captureLeaf names l = some c →
      ∃ r, (match rc with
        | Result.returned runtime' values =>
          if values.isEmpty || names.isEmpty then (pure (Result.normal runtime') : SolI Result)
          else
            match runtime'.assignNamedValues? names values with
            | some updated => pure (Result.normal updated)
            | none => pure (Result.reverted runtime' RevertData.typeMismatch)
        | result => pure result) = .done (.ok r) ∧ LeafRel ρ E ctx r (c.eval ρ)
  | .returned rt1 vals, .returned S1 vs, c, h1, h => by
    simp only [LeafRel] at h1
    obtain ⟨h1, rfl⟩ := h1
    simp only [captureLeaf] at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      have : ((vs.map fun e => Value.word (e.eval ρ)).isEmpty || names.isEmpty) = true := by
        rcases hv with rfl | rfl <;> simp
      simp only [this, ↓reduceIte]
      exact ⟨_, rfl, h1⟩
    · rename_i hv
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨sc, hsc, rfl⟩ := h
      have : ((vs.map fun e => Value.word (e.eval ρ)).isEmpty || names.isEmpty) = false := by
        cases vs <;> cases names <;> simp_all
      have ha := (assignMany_words names vs rt1 S1.scopes sc h1.frames hsc).1
      simp only [this, Bool.false_eq_true, ↓reduceIte, ha]
      exact ⟨_, rfl, { h1 with frames := rfl }⟩
  | .normal rt1, .normal S1, c, h1, h => by
    simp only [captureLeaf, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, h1⟩
  | .reverted rt1 err, .reverted p, c, h1, h => by
    simp only [captureLeaf, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, h1⟩
  | .normal _, .returned _ _, _, h1, _ | .normal _, .reverted _, _, h1, _
  | .returned _ _, .normal _, _, h1, _ | .returned _ _, .reverted _, _, h1, _
  | .reverted _ _, .normal _, _, h1, _ | .reverted _ _, .returned _ _, _, h1, _
  | .broke _, _, _, h1, _ | .continued _, _, _, h1, _ | .selfdestructed _, _, _, h1, _ => by
    first | (cases h1) | (rename_i l; cases l <;> cases h1) | skip

theorem eval_stmt (ρ : Val) (E : EraseEnv) (ctx : Context) :
    ∀ n s S b, eraseStmt E n s S = some b → ∀ rt, StmtRel ρ E ctx rt S →
      ∃ r, Stmt.eval n E.tbl ctx rt s = .done (.ok r) ∧ LeafRel ρ E ctx r (b.eval ρ) := by
  intro n
  induction n with
  | zero => intro s S b h; simp [eraseStmt] at h
  | succ n ih =>
    intro s S b h rt hrel
    cases s
    case skip =>
      simp only [eraseStmt, Option.some.injEq] at h
      subst h
      exact ⟨.normal rt, by rw [Stmt.eval]; rfl, hrel⟩
    case block ss =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b0, h0, rfl⟩ := h
      obtain ⟨r, hr, hl⟩ := eval_seq_of ρ E ctx n ih ss S.push b0 h0 rt.pushScope hrel.pushScope
      refine ⟨r.mapRuntime Runtime.popScope, ?_, ?_⟩
      · rw [Stmt.eval]
        simp only [hr, bind, EvmCompiler.Simulation.Interaction.bind]
        rfl
      · rw [Br.eval_mapS]
        exact hl.popScope
    case varDecl ty x init =>
      simp only [eraseStmt] at h
      split at h
      case isFalse => simp at h
      rename_i hty
      have hco := fun v => (wordTy_coerce hty v).1
      have hdef := (wordTy_coerce hty 0).2
      cases init with
      | none =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨.normal (rt.declareLocal x (.word 0)), ?_, ?_⟩
        · rw [Stmt.eval]
          simp only [hdef]
          rfl
        · have hf : (rt.declareLocal x (.word 0)).locals =
              (S.scopes.declare x (.lit 0)).map (frameOf ρ) := by
            rw [Runtime.declareLocal, hrel.frames]
            exact env_declare ρ S.scopes x (.lit 0)
          exact { hrel with frames := hf }
      | some e =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨gs, v⟩, he, rfl⟩ := h
        have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
        rw [Stmt.eval]
        simp only [heval, caught_exprResult, guards_eval]
        by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
        · simp only [hg, ↓reduceIte]
          exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
        · simp only [hg, Bool.false_eq_true, ↓reduceIte, bind_done_ok, hco]
          refine ⟨.normal (rt.declareLocal x (.word (v.eval ρ))), rfl, ?_⟩
          have hf : (rt.declareLocal x (.word (v.eval ρ))).locals =
              (S.scopes.declare x v).map (frameOf ρ) := by
            rw [Runtime.declareLocal, hrel.frames, env_declare]
          exact { hrel with frames := hf }
    case emitEvent name es =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨decl, hdecl, t, ht, ⟨gs, svs⟩, hes, h⟩ := h
      split at h
      case isFalse => simp at h
      rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      have hfind : ctx.eventDecl? name = some decl := by
        simp [Context.eventDecl?, hrel.events, hdecl]
      have hlist := eval_exprList ρ E.fields ctx rt S hrel.expr _ gs svs _ hes (Nat.le_refl _)
      have hlog := emit_words ρ ctx rt hfind ht hrel.facts hok
      have heq : Stmt.eval (n + 1) E.tbl ctx rt (.emitEvent name es) =
          (do
            match ← (Expr.evalList ctx rt
                ((emitSchedule (emitFlags (some decl) es) es.length).filterMap
                  (fun i => es[i]?))).caught with
            | Except.ok (scheduled, runtime') =>
                match runtime'.materializeForValueUseList ctx
                    (unschedule (emitSchedule (emitFlags (some decl) es) es.length) scheduled
                      es.length) with
                | Except.ok values =>
                    match runtime'.emitEvent ctx name values with
                    | Except.ok updated => pure (Result.normal updated)
                    | Except.error err => pure (Result.reverted rt err)
                | Except.error err => pure (Result.reverted rt err)
            | Except.error err => pure (Result.reverted rt err)) := by
        rw [Stmt.eval]
        simp only [hfind]
        rfl
      rw [heq, Expr.evalList, hlist]
      rw [guards_eval]
      by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
      · simp only [hg, ↓reduceIte]
        exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, caught_done_ok, bind_done_ok,
          unschedule_map, materialize_words]
        obtain ⟨ev, rt', hrt, hev, hloc, hsto, hl⟩ := hlog
        simp only [hrt]
        refine ⟨.normal rt', rfl, ?_⟩
        exact { hrel with
          frames := by rw [hloc, hrel.frames]
          store := fun k hk => by
            rw [← hrel.store k hk]
            simp only [State.loadSlot, hsto]
          logs := by
            rw [hev, List.map_append, hrel.logs, List.map_append]
            simp only [List.map_cons, List.map_nil, hl] }
    case captureReturn names body =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨b0, hb0, h⟩ := h
      obtain ⟨r0, hr0, hl0⟩ := ih body S b0 hb0 rt hrel
      obtain ⟨c, hc, hce⟩ := Br.bindLeaf_eval ρ h
      obtain ⟨r, hr, hl⟩ := capture_ok names r0 (b0.eval ρ) c hl0 hc
      refine ⟨r, ?_, hce ▸ hl⟩
      rw [Stmt.eval]
      simp only [hr0, bind_done_ok]
      exact hr
    case internalCall targets callee args =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨fn, hfn, h⟩ := h
      split at h
      case isFalse => simp at h
      rename_i hshape
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨gs, vs⟩, hargs, b0, hb0, b1, hb1, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hshape
      have hp : fn.params.all wordDecl = true := hshape.1.1
      have hr : fn.returns.all wordDecl = true := hshape.1.2
      have hvl : vs.length = fn.params.length := (eraseExprs_length hargs).trans hshape.2
      have hev := eval_refArgs ρ E.fields ctx rt S hrel.expr args gs vs _ hargs (Nat.le_refl _)
      rw [Stmt.eval]
      simp only [Expr.evalRefArgList, hev]
      rw [guards_eval]
      by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
      · simp only [hg, ↓reduceIte]
        exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, caught_done_ok, bind_done_ok, hfn,
          internalCallEnter?, initialFrame_words ρ fn vs hp hr hvl]
        have hctx : ({ ctx with checked := true } : Context) = ctx := by
          rw [show true = ctx.checked from hrel.checked.symm]
        have hrel0 : StmtRel ρ E ctx { rt with locals := [frameOf ρ (callFrame fn vs)] }
            { scopes := [callFrame fn vs], writes := S.writes, logs := S.logs } :=
          { hrel with frames := rfl }
        obtain ⟨r0, hr0, hl0⟩ := ih fn.body _ b0 hb0 _ hrel0
        rw [hctx, hr0, bind_done_ok]
        obtain ⟨c, hc, hce⟩ := Br.bindLeaf_eval ρ hb1
        rw [hce]
        exact finish_call hrel hr r0 _ c hl0 hc
    case panic code =>
      simp only [eraseStmt, Option.some.injEq] at h
      subst h
      exact ⟨.reverted rt (.panic code), by rw [Stmt.eval]; rfl, rfl⟩
    case requireStmt c r =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨gs, v⟩, hc, rfl⟩ := h
      have heval := eval_eq ρ E.fields ctx rt S hrel.expr hc
      rw [Stmt.eval]
      simp only [heval, caught_exprResult, guards_eval]
      by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
      · simp only [hg, ↓reduceIte]
        exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, bind_done_ok, Value.expectWord,
          norm_lt (v.eval_lt ρ), Br.eval, wordTruthy]
        by_cases hv : v.eval ρ = 0
        · cases r
          case none =>
            refine ⟨.reverted rt .empty, ?_, by simp only [hv, ↓reduceIte, LeafRel]; rfl⟩
            simp [hv]
            rfl
          case some m =>
            refine ⟨.reverted rt (.error m), ?_, by simp only [hv, ↓reduceIte, LeafRel]; rfl⟩
            simp [hv]
            rfl
        · refine ⟨.normal rt, ?_, by simp only [hv, ↓reduceIte, LeafRel]; exact hrel⟩
          simp [hv, SolidCore.Solidity.Shared.norm, modulus_eq, Nat.mod_eq_of_lt (v.eval_lt ρ)]
          rfl
    case revertError r =>
      simp only [eraseStmt, Option.some.injEq] at h
      subst h
      cases r
      case none => exact ⟨.reverted rt .empty, by rw [Stmt.eval]; rfl, rfl⟩
      case some m => exact ⟨.reverted rt (.error m), by rw [Stmt.eval]; rfl, rfl⟩

    case assign target e =>
      cases target
      case var x =>
        simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨gs, v⟩, he, L', hL, rfl⟩ := h
        obtain ⟨old, hold⟩ := Scopes.get?_of_set hL
        have hx : rt.lookupLocal? x = some (.word (old.eval ρ)) := hrel.expr.locals x old hold
        have hmem : rt.lookupMemoryRef? x = none := by simp [Runtime.lookupMemoryRef?, hx]
        have hbase : rt.lookupStorageBase? x = none := by simp [Runtime.lookupStorageBase?, hx]
        have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
        have hres : LValue.resolveWithRuntime (.var x) ctx rt = .done (.ok (.local x, rt)) := by
          simp [LValue.resolveWithRuntime, Expr.resolveLValue, LValue.toExpr, Expr.orderFuel,
            Expr.resolveLValueFuel, hbase, hx]
          rfl
        have hassign : rt.assignLocal? x (.word (v.eval ρ)) =
            some { rt with locals := L'.map (frameOf ρ) } := by
          simp [Runtime.assignLocal?, hx, Value.coerceLike?, hrel.frames, env_assign ρ S.scopes x v, hL]
        have hrel' : StmtRel ρ E ctx { rt with locals := L'.map (frameOf ρ) }
            { S with scopes := L' } := { hrel with frames := rfl }
        rw [Stmt.eval]
        simp only [LValue.wantsMemoryRefRhs, hmem, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte, heval, caught_exprResult]
        rw [guards_eval]
        by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
        · simp only [hg, ↓reduceIte]
          refine ⟨.reverted rt (.panic 0x11), ?_, rfl⟩
          split <;> (try split) <;> first | rfl | simp_all
        · simp only [hg, Bool.false_eq_true, ↓reduceIte]
          refine ⟨.normal { rt with locals := L'.map (frameOf ρ) }, ?_, hrel'⟩
          split
          · split
            · simp_all
            · simp only [bind_done_ok, hres, caught_done_ok, ite_self, ResolvedLValue.write, hassign]
              rfl
          · simp only [bind_done_ok, hres, caught_done_ok, ite_self, ResolvedLValue.write, hassign]
            rfl
      case storageIndex x i =>
        simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨gs, v⟩, he, ⟨gi, key⟩, hi, h⟩ := h
        obtain ⟨k, hk, hst, rfl⟩ : ∃ k, k < wordSize ∧
            rt.storeStorageIndexWithDeepClear ctx x (.word (key.eval ρ)) (.word (v.eval ρ)) =
              .ok { rt with state := rt.state.storeSlot (solHash (key.eval ρ) k) (v.eval ρ) } ∧
            b = guards (gs ++ gi)
              (.leaf (.normal { S with writes := S.writes.set (.hash key (.lit k)) v })) := by
          split at h
          · rename_i k hk
            simp only [Option.some.injEq] at h
            obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk
            exact ⟨f.slot, hf.slot, storeIndex_map hrel hk (key.eval_lt ρ) (v.eval_lt ρ), h.symm⟩
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨k, hk, h⟩ := h
            split at h
            · rename_i hb
              simp only [Option.some.injEq] at h
              obtain ⟨f, hf, rfl⟩ := boolMapOf?_spec hrel.fields hk
              exact ⟨f.slot, hf.slot, storeIndex_boolMap hrel hk (key.eval_lt ρ)
                (Nat.le_trans (bound_sound hrel.facts v) hb), h.symm⟩
            · simp at h
        have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
        have hres := resolve_storageIndex ρ E.fields ctx rt S hrel.expr x hi
        have hsl : (WExpr.hash key (.lit k)).eval ρ = solHash (key.eval ρ) k % wordSize := by
          simp only [WExpr.eval, hrel.hash, Nat.mod_eq_of_lt hk]
        have hw := hrel.write (.hash key (.lit k)) v
        rw [hsl, storeSlot_mod] at hw
        rw [Stmt.eval]
        simp only [LValue.wantsMemoryRefRhs, Bool.false_eq_true, ↓reduceIte, heval, caught_exprResult]
        rw [guards_eval]
        simp only [any_append]
        by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
        · simp only [hg, Bool.true_or, ↓reduceIte]
          exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
        · simp only [hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte, bind_done_ok, hres]
          by_cases hgi : gi.any (fun g => g.eval ρ != 0) = true
          · simp only [hgi, ↓reduceIte]
            exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
          · simp only [hgi, Bool.false_eq_true, ↓reduceIte, bind_done_ok, ResolvedLValue.write, hst,
              ite_self]
            exact ⟨_, rfl, hw⟩
      case index base i2 =>
        cases base
        case storageIndex x i1 =>
          simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨k, hk, ⟨gs, v⟩, he, ⟨g1, k1⟩, h1, ⟨g2, k2⟩, h2, rfl⟩ := h
          obtain ⟨f, hf, rfl⟩ := map2Of?_spec hrel.fields hk
          have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
          have hres := resolve_index2 ρ E.fields ctx rt S hrel.expr x h1 h2
          simp only [any_append] at hres
          have hsl : (WExpr.hash k2 (.hash k1 (.lit f.slot))).eval ρ =
              solHash (k2.eval ρ) (solHash (k1.eval ρ) f.slot) % wordSize := by
            simp only [WExpr.eval, hrel.hash, Nat.mod_eq_of_lt hf.slot,
              Nat.mod_eq_of_lt (solHash_lt _ _)]
          have hw := hrel.write (.hash k2 (.hash k1 (.lit f.slot))) v
          rw [hsl, storeSlot_mod] at hw
          have hst := storePath_map2 hrel hk (k1.eval_lt ρ) (k2.eval_lt ρ) (v.eval_lt ρ)
          rw [Stmt.eval]
          simp only [LValue.wantsMemoryRefRhs, LValue.toExpr, Expr.hasStorageRoot, Bool.true_or,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval, caught_exprResult]
          rw [guards_eval]
          simp only [any_append]
          by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
          · simp only [hg, Bool.true_or, ↓reduceIte]
            exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
          · simp only [hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte, bind_done_ok, hres]
            by_cases hgi : (g1.any (fun g => g.eval ρ != 0) || g2.any (fun g => g.eval ρ != 0)) = true
            · simp only [hgi, ↓reduceIte, Bool.or_assoc]
              exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
            · simp only [hgi, Bool.or_assoc, Bool.false_eq_true, ↓reduceIte, bind_done_ok,
                ResolvedLValue.write, hst, ite_self]
              exact ⟨_, rfl, hw⟩
        all_goals simp [eraseStmt] at h
      case storage x =>
        simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨k, off, bytes⟩, hk, ⟨gs, v⟩, he, rfl⟩ := h
        obtain ⟨f, hfx, rfl, rfl, rfl⟩ := fieldOf?_spec hrel.fields hk
        have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
        have hres : LValue.resolveWithRuntime (.storage x) ctx rt =
            .done (.ok (.storageField x, rt)) := by
          simp [LValue.resolveWithRuntime, Expr.resolveLValue, LValue.toExpr, Expr.orderFuel,
            Expr.resolveLValueFuel]
          rfl
        have hw := v.eval_lt ρ
        have hsl : rt.state.loadSlot f.slot = (S.writes.read (.lit f.slot)).eval ρ :=
          slot_read hrel.expr hfx.slot
        have hslw : rt.state.loadSlot f.slot < wordSize := hsl ▸ WExpr.eval_lt _ _
        have hrelw := hrel.writeField hfx v
        rw [Stmt.eval]
        simp only [LValue.wantsMemoryRefRhs, Bool.false_eq_true, ↓reduceIte, heval, caught_exprResult]
        rw [guards_eval]
        by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
        · simp only [hg, ↓reduceIte]
          exact ⟨.reverted rt (.panic 0x11), by split <;> rfl, rfl⟩
        · simp only [hg, Bool.false_eq_true, ↓reduceIte]
          refine ⟨.normal _, ?_, hrelw⟩
          simp only [bind_done_ok, hres, caught_done_ok, ResolvedLValue.write,
            store_field hfx hslw _ hw, ite_self, writeField_eval ρ _ _ hfx.fits hfx.bytes, hsl]
          rfl
      all_goals simp [eraseStmt] at h
    case returnValues es =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨gs, vs⟩, hes, rfl⟩ := h
      have hlen : es.length < Expr.listEvalFuel es := by
        clear hes
        induction es with
        | nil => simp [Expr.listEvalFuel]
        | cons e es ihl => simp only [List.length_cons, Expr.listEvalFuel]; omega
      have hl := eval_returnList ρ E.fields ctx rt S hrel.expr es gs vs _ hes hlen
      rw [Stmt.eval]
      simp only [Expr.evalReturnList, hl, guards_eval]
      by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
      · simp only [hg, ↓reduceIte]
        exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
        exact ⟨.returned rt (vs.map fun e => Value.word (e.eval ρ)), rfl, hrel, rfl⟩
    case ifElse c t e =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨gs, v⟩, hc, bt, hbt, be, hbe, rfl⟩ := h
      have heval := eval_eq ρ E.fields ctx rt S hrel.expr hc
      rw [Stmt.eval]
      simp only [heval, caught_exprResult, guards_eval]
      by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
      · simp only [hg, ↓reduceIte]
        exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, bind_done_ok, Value.expectWord,
          norm_lt (v.eval_lt ρ), Br.eval, wordTruthy]
        by_cases hv : v.eval ρ = 0
        · obtain ⟨r, hr, hl⟩ := ih e S be hbe rt hrel
          refine ⟨r, ?_, by simpa [hv] using hl⟩
          simp [hv, hr]
        · obtain ⟨r, hr, hl⟩ := ih t S bt hbt rt hrel
          refine ⟨r, ?_, by simpa [hv] using hl⟩
          simp [hv, hr]
    case exprStmt ex =>
      cases ex
      case assignment op? cleanup? target rhs =>
        cases target
        case storageRead m x idx =>
          cases m
          case element =>
            rcases idx with _ | ⟨i, _ | ⟨_, _⟩⟩ <;> rcases op? with _ | op <;>
              rcases cleanup? with _ | c
            all_goals first | (simp [eraseStmt] at h; done) | skip
            cases c <;> (try (simp [eraseStmt] at h; done))
            simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨k, hk, ⟨gs, v⟩, hv, ⟨gi, key⟩, hi, o, ho, cg, hcg, rfl⟩ := h
            exact eval_mapAssign ρ E ctx rt S hrel n hk hv hi ho hcg
          all_goals cases idx <;> simp only [eraseStmt] at h
          all_goals first | (simp at h; done) | skip
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨k, off, bytes⟩, hk, ⟨gs, v⟩, hv, h⟩ := h
          obtain ⟨f, hfx, rfl, rfl, rfl⟩ := fieldOf?_spec hrel.fields hk
          have heval := eval_erase ρ E.fields ctx rt S hrel.expr rhs gs v
            ((Expr.storageRead .header x []).orderFuel + rhs.orderFuel + 1) hv (by omega)
          have hres : Expr.resolveLValueFuel ((Expr.storageRead .header x []).orderFuel +
              rhs.orderFuel + 1) ctx rt (.storageRead .header x []) =
              .done (.ok (.storageField x, rt)) := by
            simp [Expr.orderFuel, Expr.listEvalFuel, Expr.resolveLValueFuel]
            rfl
          rw [Stmt.eval]
          simp only [Expr.eval, Expr.orderFuel] at heval hres ⊢
          generalize Expr.listEvalFuel [] + 1 + rhs.orderFuel + 1 = F at heval hres ⊢
          rw [Expr.evalFuel]
          simp only [heval, bind_exprResult, hres, bind_done_ok]
          have hw := v.eval_lt ρ
          have hsl : rt.state.loadSlot f.slot = (S.writes.read (.lit f.slot)).eval ρ :=
            slot_read hrel.expr hfx.slot
          have hslw : rt.state.loadSlot f.slot < wordSize := hsl ▸ WExpr.eval_lt _ _
          have hst : ∀ w : WExpr, ResolvedLValue.write ctx rt (.storageField x) (.word (w.eval ρ)) =
              .ok { rt with state := (rt.state.storeSlot f.slot
                ((writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes).eval ρ)) } := by
            intro w
            simp only [ResolvedLValue.write, store_field hfx hslw _ (w.eval_lt ρ),
              writeField_eval ρ _ _ hfx.fits hfx.bytes, hsl]
          cases op? <;> cases cleanup? <;> simp only [Option.some.injEq, reduceCtorEq] at h
          case none.none =>
            subst h
            rw [guards_eval]
            by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
            · simp only [hg, ↓reduceIte]
              exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
            · simp only [hg, Bool.false_eq_true, ↓reduceIte, hst v]
              exact ⟨_, rfl, hrel.writeField hfx v⟩
          case some.some op c =>
            cases c <;> simp only [reduceCtorEq] at h
            rename_i b
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨o, ho, cg, hcg, h⟩ := h
            simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hb0, hb, hcgv⟩ := cleanupGuard_spec ρ hcg
            have hread : ResolvedLValue.read ctx rt (.storageField x) =
                .ok (.word ((readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes).eval ρ)) := by
              simp [ResolvedLValue.read, ResolvedLValue.readRaw, load_field hfx hslw, hsl,
                Runtime.derefMemoryValue, bind, Except.bind, readField_eval ρ _ hfx.fits hfx.bytes]
            have hcl : ∀ w : WExpr, ValueCleanup.apply true (.uint b) (.word (w.eval ρ)) =
                if w.eval ρ < 2 ^ b then .ok (.word (w.eval ρ)) else .error (.panic 0x11) :=
              fun w => uintCleanup_lt _ _ (w.eval_lt ρ) hb0 hb
            rw [guards_eval]
            simp only [any_append, hread, hrel.checked, liftM, monadLift, MonadLift.monadLift,
              SolI.ofExcept, bind_done_ok, apply_erased ρ ho, hcgv]
            by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
            · simp only [hg, Bool.true_or, ↓reduceIte]
              exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
            · simp only [hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
              by_cases ho' : (overflow o (readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes)
                  v).toList.any (fun g => g.eval ρ != 0) = true
              · simp only [ho', Bool.true_or, ↓reduceIte]
                exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
              · simp only [ho', Bool.false_or, Bool.false_eq_true, ↓reduceIte, bind_done_ok]
                have hcl' := hcl (.bin o (readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes) v)
                cases op
                all_goals first | (simp [binOf] at ho; done) | skip
                all_goals
                dsimp only
                rw [hcl']
                by_cases hc : (WExpr.bin o (readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes)
                    v).eval ρ < 2 ^ b
                · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                    bind_done_ok, hst]
                  exact ⟨_, rfl, hrel.writeField hfx _⟩
                · simp only [hc, decide_false, Bool.not_false, ↓reduceIte]
                  exact ⟨.reverted rt (.panic 0x11), rfl, rfl⟩
        all_goals simp [eraseStmt] at h
        all_goals simp [eraseStmt] at h
      all_goals simp [eraseStmt] at h
    all_goals simp [eraseStmt] at h


end SolidCore.Refinement.Generic

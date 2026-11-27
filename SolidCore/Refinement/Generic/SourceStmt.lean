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

/-- Assign the word `e` to the local `x` the state holds as a word: none for a typed local. -/
def SymState.setW (S : SymState) (x : String) (e : WExpr) : Option Scopes :=
  if S.tags.get x = .word then Scopes.set S.scopes x e else none

/-- Assign words to locals the state holds as words, one after the other: none when one of them is
typed. -/
def SymState.setManyW (S : SymState) (xs : List String) (es : List WExpr) : Option Scopes :=
  if xs.all (fun x => S.tags.get x == .word) then Scopes.setMany S.scopes xs es else none

/-- The caller's state after an internal call returned the words `ws`: the call's targets
assigned, the callee's writes and logs. -/
def callAssign (targets : List String) (S S1 : SymState) (ws : List WExpr) : Option Br :=
  if targets = [] then some (.leaf (.normal { S with writes := S1.writes, logs := S1.logs }))
  else do
    let sc ← S.setManyW targets ws
    let S2 : SymState := { scopes := sc, writes := S1.writes, logs := S1.logs, caller := S.caller, tags := S.tags }
    some (.leaf (.normal S2))

/-- The end of an internal call from the end of its callee's body: its named returns or its
returned words assigned to the targets, or the callee's revert. -/
def callLeaf (fn : InternalFunction) (targets : List String) (S : SymState) : Leaf → Option Br
  | .normal S1 => do
    let ws ← fn.returns.mapM fun r => S1.word? r.name
    callAssign targets S S1 ws
  | .returned S1 vs =>
    if vs = [] then do
      let ws ← fn.returns.mapM fun r => S1.word? r.name
      callAssign targets S S1 ws
    else if vs.length = fn.returns.length then callAssign targets S S1 vs
    else none
  | .reverted p => some (.leaf (.reverted p))

/-- The end of a `captureReturn`: a return of words assigned to its names. -/
def captureLeaf (names : List String) : Leaf → Option Br
  | .returned S1 vs =>
    if vs = [] ∨ names = [] then some (.leaf (.normal S1))
    else do
      let sc ← S1.setManyW names vs
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

/-! ## `unchecked` blocks of the fragment

An `unchecked` block of the fragment is SafeMath's check of a wrapped result: one
`require((z = a op b) cmp c, msg)` whose local `z` takes the wrapped `a op b` (`+` or `-`
of locals, no overflow check) and whose condition compares it with `c` (`>=`, `<=` or
`!=`). SolidCore evaluates the right operand `c` first, then the assignment. -/

/-- The wrapping operators of an `unchecked` block of the fragment. -/
def wrapOf : BinaryOp → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | _ => none

/-- The word of an expression of an `unchecked` block of the fragment: locals under `uint256`
cleanups and wrapping `+` and `-` of them, none of which reverts. -/
def wrapRead (S : SymState) : Expr → Option WExpr
  | .var x => S.word? x
  | .castOp .uintCleanup 256 e => wrapRead S e
  | .binary op l r => do
    let o ← wrapOf op
    let vl ← wrapRead S l
    let vr ← wrapRead S r
    some (.bin o vl vr)
  | _ => none

/-- The word of `a >= b`, `a <= b` or `a != b`, with `<=` as solar compares, by `lt` of the
swapped operands. -/
def cmpOf : BinaryOp → WExpr → WExpr → Option WExpr
  | .ge, a, b => some (.un .iszero (.bin .lt a b))
  | .le, a, b => some (.un .iszero (.bin .lt b a))
  | .ne, a, b => some (.un .iszero (.bin .eq a b))
  | _, _, _ => none

/-- A `require` condition `(z = rhs) cmp c` of an `unchecked` block of the fragment: the local `z`,
its new word and the condition's word. -/
def uncheckedCond (S : SymState) : Expr → Option (String × WExpr × WExpr)
  | .binary cmp (.castOp .uintCleanup 256 (.assignment none none (.var z) rhs)) c => do
    let vc ← wrapRead S c
    let w ← wrapRead S rhs
    let v ← cmpOf cmp w vc
    some (z, w, v)
  | _ => none

/-- The erasure of the body of an `unchecked` block of the fragment: a block of one `require`
whose condition assigns a local, as SafeMath's `add` and `sub` check their wrapped result. -/
def eraseUnchecked (S : SymState) : Stmt → Option Br
  | .block [.requireStmt c r] => do
    let (z, w, v) ← uncheckedCond S.push c
    let L ← S.push.setW z w
    some (Br.mapS SymState.pop
      (.ite v (.leaf (.normal { S.push with scopes := L })) (.leaf (.reverted (failOf r)))))
  | _ => none

/-- The erasure of a statement of the fragment with fuel `n`, the fuel SolidCore runs it with:
skips, blocks (a scope each), assignments to locals and to storage fields, compound assignments
to storage fields (`v += x`, `w ^= x`: the operation's overflow check, then the cleanup's range
check), increments and decrements of storage fields as statements (`v++`, `--v`: the same with
the word 1), expression statements of an expression of the fragment (`y;`: its overflow checks, then
the state unchanged), returns, `if`, panics and SafeMath's `unchecked` blocks
(`eraseUnchecked`). -/
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
      let L ← S.setW x v
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
    | .exprStmt (.incDec op _ (some (.uint b)) (.storageRead .header x [])) => do
      let (k, off, bytes) ← fieldOf? E.fields x
      let o ← binOf op
      let w := WExpr.bin o (readField (S.writes.read (.lit k)) off bytes) (.lit 1)
      let cg ← cleanupGuard b w
      some (guards ((overflow o (readField (S.writes.read (.lit k)) off bytes) (.lit 1)).toList ++ cg)
        (.leaf (.normal
          { S with writes := S.writes.set (.lit k) (writeField (S.writes.read (.lit k)) w off bytes) })))
    | .exprStmt e => do
      let (gs, _) ← eraseExpr E.fields S e
      some (guards gs (.leaf (.normal S)))
    | .varDecl ty x init =>
      if wordTy ty ∧ S.tags.get x = .word then
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
        let b ← eraseStmt E n fn.body { scopes := [callFrame fn vs], writes := S.writes, logs := S.logs, caller := S.caller }
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
    | .unchecked body => if 2 ≤ n then eraseUnchecked S body else none
    | _ => none


/-! ## The relation between SolidCore's runtime and a symbolic state -/

/-- A scope of a function's locals, as SolidCore holds it. -/
def frameOf (ρ : Val) (L : Locals) : Frame := L.map fun p => (p.1, Value.word (p.2.eval ρ))

/-- A scope of a function's locals, as SolidCore holds it, each local by its tag: a word, a signed
word or a `bytes32`. -/
def frameOfT (ρ : Val) (T : Tags) (L : Locals) : Frame :=
  L.map fun p => (p.1, (T.get p.1).val (p.2.eval ρ))

@[simp] theorem frameOfT_nil (ρ : Val) : frameOfT ρ [] = frameOf ρ := rfl

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
  sender : ctx.sender = S.caller.eval ρ
  hash : ρ.hash = solHash
  ok : ρ.Ok
  frames : rt.locals = S.scopes.map (frameOfT ρ S.tags)
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

theorem frameT_lookup (ρ : Val) (T : Tags) (L : Locals) (x : String) :
    Frame.lookup? (frameOfT ρ T L) x = (L.get? x).map fun e => (T.get x).val (e.eval ρ) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨y, e⟩ := p
    simp only [frameOfT, List.map_cons, Frame.lookup?, Locals.get?] at ih ⊢
    by_cases h : y = x
    · subst h; simp
    · simp [h, ih]

theorem envT_lookup (ρ : Val) (T : Tags) : ∀ (sc : Scopes) (x : String),
    LocalEnv.lookup? (sc.map (frameOfT ρ T)) x = (Scopes.get? sc x).map fun e => (T.get x).val (e.eval ρ)
  | [], _ => rfl
  | L :: rest, x => by
    simp only [List.map_cons, LocalEnv.lookup?, frameT_lookup, Scopes.get?]
    cases L.get? x with
    | some e => rfl
    | none => exact envT_lookup ρ T rest x

/-- A word local's lookup in a typed scope. -/
theorem lookup_word {ρ : Val} {rt : Runtime} {S : SymState}
    (hfr : rt.locals = S.scopes.map (frameOfT ρ S.tags)) {x : String} {e : WExpr}
    (he : S.word? x = some e) : rt.lookupLocal? x = some (.word (e.eval ρ)) := by
  unfold SymState.word? at he
  split at he
  · rename_i ht
    simp [Runtime.lookupLocal?, hfr, envT_lookup, he, ht]
  · simp at he

theorem frameT_assign (ρ : Val) (T : Tags) (L : Locals) (x : String) (v : WExpr)
    (hx : T.get x = .word) :
    Frame.assign? (frameOfT ρ T L) x (Value.word (v.eval ρ)) = (L.set x v).map (frameOfT ρ T) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨y, e⟩ := p
    by_cases hy : y = x
    · subst hy; simp [frameOfT, Frame.assign?, Locals.set, hx]
    · simp only [frameOfT, List.map_cons, Frame.assign?, Locals.set, hy, ↓reduceIte] at ih ⊢
      rw [ih]
      cases Locals.set L x v <;> rfl

theorem envT_assign (ρ : Val) (T : Tags) (x : String) (v : WExpr) (hx : T.get x = .word) :
    ∀ (sc : Scopes), LocalEnv.assign? (sc.map (frameOfT ρ T)) x (Value.word (v.eval ρ)) =
      (Scopes.set sc x v).map (·.map (frameOfT ρ T))
  | [] => rfl
  | L :: rest => by
    simp only [List.map_cons, LocalEnv.assign?, frameT_assign ρ T L x v hx, Scopes.set]
    cases L.set x v with
    | some L' => rfl
    | none =>
      simp only [Option.map_none, envT_assign ρ T x v hx rest]
      cases Scopes.set rest x v <;> rfl

theorem envT_declare (ρ : Val) (T : Tags) (sc : Scopes) (x : String) (v : WExpr)
    (hx : T.get x = .word) :
    LocalEnv.declare (sc.map (frameOfT ρ T)) x (Value.word (v.eval ρ)) =
      (sc.declare x v).map (frameOfT ρ T) := by
  cases sc <;> simp [LocalEnv.declare, Scopes.declare, frameOfT, hx]

theorem SymState.setW_spec {S : SymState} {x : String} {v : WExpr} {L : Scopes}
    (h : S.setW x v = some L) : S.tags.get x = .word ∧ Scopes.set S.scopes x v = some L := by
  unfold SymState.setW at h
  split at h
  · exact ⟨by assumption, h⟩
  · simp at h

theorem SymState.setManyW_spec {S : SymState} {xs : List String} {es : List WExpr} {L : Scopes}
    (h : S.setManyW xs es = some L) :
    (∀ x ∈ xs, S.tags.get x = .word) ∧ Scopes.setMany S.scopes xs es = some L := by
  unfold SymState.setManyW at h
  split at h
  · rename_i ha
    refine ⟨fun x hx => ?_, h⟩
    have := List.all_eq_true.mp ha x hx
    simpa using this
  · simp at h

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
  locals x e he := lookup_word h.frames he
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

/-- Split on whether the overflow conditions `c` fire: then the statement reverts with
`Panic(0x11)`, as its guarded leaf does; otherwise go on past them. -/
local macro "guard_cases " h:ident " : " c:term : tactic => `(tactic|
  (by_cases $h:ident : $c = true
   focus
     simp only [$h:ident, ↓reduceIte, Bool.true_or, Bool.or_true, Bool.or_assoc]
     first
       | exact ⟨_, rfl, rfl⟩
       | exact ⟨.reverted _ (.panic 0x11), by split <;> (try split) <;> first | rfl | simp_all, rfl⟩
   simp only [$h:ident, Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false,
     Bool.or_assoc]))

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
  { h with frames := by simp [Runtime.pushScope, SymState.push, h.frames, frameOfT] }

theorem caught_done_ok {α : Type} (a : α) :
    SolI.caught (EvmCompiler.Simulation.Interaction.done (.ok a) : SolI α) =
      EvmCompiler.Simulation.Interaction.done (.ok (.ok a)) := rfl

theorem bind_done_ok {α β : Type} (a : α) (k : α → SolI β) :
    ((EvmCompiler.Simulation.Interaction.done (.ok a) : SolI α) >>= k) = k a := rfl

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

/-- A word field reads its `readField` and writes its `writeField` of the slot's symbolic word. -/
theorem StmtRel.field_rw {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {x : String} {f : StorageField} (hfx : FieldOk ctx x f) :
    ResolvedLValue.read ctx rt (.storageField x) =
        .ok (.word ((readField (S.writes.read (.lit f.slot)) f.packedOffset f.packedBytes).eval ρ)) ∧
      ∀ (w : WExpr) (sx : Bool), rt.storeStorageFieldWithDeepClear ctx x (.word (w.eval ρ)) sx =
        .ok { rt with state := (rt.state.storeSlot f.slot
          ((Generic.writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes).eval ρ)) } := by
  have hsl : rt.state.loadSlot f.slot = (S.writes.read (.lit f.slot)).eval ρ :=
    slot_read hrel.expr hfx.slot
  have hslw : rt.state.loadSlot f.slot < wordSize := hsl ▸ WExpr.eval_lt _ _
  refine ⟨?_, fun w sx => ?_⟩
  · simp [ResolvedLValue.read, ResolvedLValue.readRaw, load_field hfx hslw, hsl,
      Runtime.derefMemoryValue, bind, Except.bind, readField_eval ρ _ hfx.fits hfx.bytes]
  · simp only [store_field hfx hslw _ (w.eval_lt ρ), writeField_eval ρ _ _ hfx.fits hfx.bytes, hsl]

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
  all_goals simp only [apply_bitAnd _ _ hl hr, apply_bitOr _ _ hl hr, apply_bitXor _ _ hl hr,
    apply_lt _ _ hl hr, apply_gt _ _ hl hr, apply_eq _ _ hl hr, overflow, Option.toList_none,
    List.any_nil, Bool.false_eq_true, ↓reduceIte, WExpr.eval, BinOp.eval]
  all_goals split_ifs <;> rfl

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

/-- A left-to-right evaluator of expressions of the fragment, whose step gives each expression's
erased word without touching the runtime, gives the list's words after their overflow conditions.
`Expr.evalListFuel`, `Expr.evalReturnListFuel` and `Expr.evalRefArgListFuel` are such
evaluators. -/
theorem eval_wordList (ρ : Val) (fields : List StorageField) (S : SymState) (rt : Runtime)
    (F : Nat → Runtime → List Expr → SolI (List Value × Runtime))
    (step : Nat → Expr → SolI (Value × Runtime))
    (hF : ∀ n e es, F (n + 1) rt (e :: es) = (do
      let (v, rt1) ← step n e
      let (vs, rt2) ← F n rt1 es
      pure (v :: vs, rt2)))
    (hnil : ∀ n, F (n + 1) rt [] = pure ([], rt))
    (hstep : ∀ n e g v, eraseExpr fields S e = some (g, v) → e.orderFuel < n →
      step n e = exprResult ρ g v rt) :
    ∀ (es : List Expr) (gs vs : List WExpr) (fuel : Nat), eraseExprs fields S es = some (gs, vs) →
      Expr.listEvalFuel es ≤ fuel →
      F fuel rt es =
        if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
        else .done (.ok (vs.map (fun e => Value.word (e.eval ρ)), rt)) := by
  intro es
  induction es with
  | nil =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [Expr.listEvalFuel] at hf; omega⟩
    simp only [eraseExprs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hnil n
  | cons e es ih =>
    intro gs vs fuel h hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [Expr.listEvalFuel] at hf; omega⟩
    simp only [eraseExprs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨g, v⟩, he, ⟨gs', vs'⟩, hes, rfl, rfl⟩ := h
    simp only [Expr.listEvalFuel] at hf
    have hpos : 1 ≤ Expr.listEvalFuel es := by cases es <;> simp [Expr.listEvalFuel]
    rw [hF, hstep n e g v he (by omega), bind_exprResult, List.any_append]
    by_cases h1 : g.any (fun g => g.eval ρ != 0) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      rw [ih gs' vs' n hes (by omega)]
      by_cases h2 : gs'.any (fun g => g.eval ρ != 0) = true <;> simp [h2] <;> rfl

/-- A local of the fragment holds a word: it is neither a memory reference nor a storage base. -/
theorem var_refs {ρ : Val} {fields : List StorageField} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : ExprRel ρ fields ctx rt S) {x : String} {g : List WExpr} {v : WExpr}
    (he : eraseExpr fields S (.var x) = some (g, v)) :
    rt.lookupMemoryRef? x = none ∧ rt.lookupStorageBase? x = none := by
  simp only [eraseExpr, Option.map_eq_some_iff] at he
  obtain ⟨ex, hex, -⟩ := he
  have hl := hrel.locals x ex hex
  exact ⟨by simp [Runtime.lookupMemoryRef?, hl], by simp [Runtime.lookupStorageBase?, hl]⟩

theorem eval_returnList (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) {es : List Expr} {gs vs : List WExpr}
    (h : eraseExprs fields S es = some (gs, vs)) :
    Expr.evalReturnList ctx rt es =
      if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
      else .done (.ok (vs.map (fun e => Value.word (e.eval ρ)), rt)) :=
  eval_wordList ρ fields S rt (Expr.evalReturnListFuel · ctx) (fun _ => Expr.evalReturnValue ctx rt)
    (fun _ _ _ => by simp only [Expr.evalReturnListFuel]) (fun _ => by simp only [Expr.evalReturnListFuel])
    (fun _ e g v he _ => by
      unfold Expr.evalReturnValue
      split
      · simp only [(var_refs hrel he).1]; exact eval_eq ρ fields ctx rt S hrel he
      · exact eval_eq ρ fields ctx rt S hrel he)
    es gs vs _ h le_rfl


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

/-- A compound assignment `target op= rhs` with a `uint b` cleanup, whose target resolves to `lv`
after the overflow conditions `gi` and holds the word `cur`: the right side's overflow
conditions, the target's, the operation's and the cleanup's range check, then the write of the
new word, which `wr` and `S'` relate. -/
theorem eval_compound (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) {op : BinaryOp} {b : Nat} {target rhs : Expr}
    {gs gi cg : List WExpr} {v cur : WExpr} {o : BinOp} {lv : ResolvedLValue}
    {wr : WExpr → Runtime} {S' : WExpr → SymState}
    (hv : eraseExpr E.fields S rhs = some (gs, v))
    (hres : ∀ F, target.orderFuel < F → Expr.resolveLValueFuel F ctx rt target =
      if gi.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
      else .done (.ok (lv, rt)))
    (ho : binOf op = some o) (hcg : cleanupGuard b (.bin o cur v) = some cg)
    (hrd : lv.read ctx rt = .ok (.word (cur.eval ρ)))
    (hwr : ∀ w : WExpr, lv.write ctx rt (.word (w.eval ρ)) = .ok (wr w))
    (hrelw : ∀ w, StmtRel ρ E ctx (wr w) (S' w)) :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.assignment (some op) (some (.uint b)) target rhs)) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((guards (gs ++ gi ++ (overflow o cur v).toList ++ cg)
        (.leaf (.normal (S' (.bin o cur v))))).eval ρ) := by
  obtain ⟨hb0, hb, hcgv⟩ := cleanupGuard_spec ρ hcg
  have hcl : ValueCleanup.apply true (.uint b) (.word ((WExpr.bin o cur v).eval ρ)) =
      if (WExpr.bin o cur v).eval ρ < 2 ^ b then .ok (.word ((WExpr.bin o cur v).eval ρ))
      else .error (.panic 0x11) := uintCleanup_lt _ _ (WExpr.eval_lt ρ _) hb0 hb
  rw [Stmt.eval]
  simp only [Expr.eval, Expr.orderFuel]
  rw [Expr.evalFuel, eval_erase ρ E.fields ctx rt S hrel.expr rhs gs v _ hv (by omega),
    bind_exprResult, guards_eval]
  simp only [any_append]
  guard_cases hg : gs.any (fun g => g.eval ρ != 0)
  rw [hres _ (by omega)]
  guard_cases hgi : gi.any (fun g => g.eval ρ != 0)
  simp only [bind_done_ok, pure, EvmCompiler.Simulation.Interaction.pure, liftM, monadLift,
    MonadLift.monadLift, SolI.ofExcept, hrd, hrel.checked, apply_erased ρ ho, hcgv]
  guard_cases ho' : (overflow o cur v).toList.any (fun g => g.eval ρ != 0)
  simp only [bind_done_ok]
  cases op
  all_goals first | (simp [binOf] at ho; done) | skip
  all_goals
  dsimp only
  rw [hcl]
  by_cases hc : (WExpr.bin o cur v).eval ρ < 2 ^ b
  · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_done_ok, hwr]
    exact ⟨_, rfl, hrelw _⟩
  · simp only [hc, decide_false, Bool.not_false, ↓reduceIte]
    exact ⟨_, rfl, rfl⟩

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
  obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk
  have hsl : (WExpr.hash key (.lit f.slot)).eval ρ = solHash (key.eval ρ) f.slot % wordSize := by
    simp only [WExpr.eval, hrel.hash, Nat.mod_eq_of_lt hf.slot]
  refine eval_compound ρ E ctx rt S hrel n (lv := .storageIndex x (.word (key.eval ρ)))
    (wr := fun w => { rt with state := rt.state.storeSlot ((WExpr.hash key (.lit f.slot)).eval ρ) (w.eval ρ) })
    (S' := fun w => { S with writes := S.writes.set (.hash key (.lit f.slot)) w })
    hv (fun F hF => ?_) ho hcg ?_ (fun w => ?_) (fun w => hrel.write _ w)
  · obtain ⟨m, rfl⟩ : ∃ m, F = m + 1 := ⟨F - 1, by omega⟩
    simp only [Expr.orderFuel, Expr.listEvalFuel] at hF
    rw [Expr.resolveLValueFuel]
    simp only []
    rw [eval_erase ρ E.fields ctx rt S hrel.expr i gi key _ hi (by omega), bind_exprResult]
    rfl
  · simp [ResolvedLValue.read, ResolvedLValue.readRaw, loadIndex_map hrel.expr hk (key.eval_lt ρ),
      Writes.eval_read hrel.ok, hsl, Runtime.derefMemoryValue, bind, Except.bind]
  · simp only [ResolvedLValue.write, storeIndex_map hrel hk (key.eval_lt ρ) (w.eval_lt ρ), hsl,
      storeSlot_mod]

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

/-- A storage-to-storage copy into a mapping's entry (`m[i] = n` with a storage right side) stores
through the entry's storage path, with or without sign extension, the same word
`storeIndex_map` stores. -/
theorem storeBase_map {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {x : String} {k : Nat}
    (hk : mapOf? E.fields x = some k) {w v : Nat} (hw : w < wordSize) (hv : v < wordSize)
    (se : Bool) :
    rt.storeStorageBasePathWithDeepClear ctx (.field x) [.word w] (.word v) se =
      .ok { rt with state := rt.state.storeSlot (solHash w k) v } := by
  obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk
  rw [Runtime.storeStorageBasePathWithDeepClear]
  simp only [Runtime.storageMaterializedValue, Runtime.derefMemoryValueDeep,
    Runtime.derefMemoryValueWithFuel, bind, Except.bind, pure, Except.pure]
  rw [resolve_map hf hw]
  cases se <;>
  simp [State.storeStorageLayoutAtWithDeepClear, State.storeStorageLayoutAtWithDeepClearFuelMode,
    State.storeStorageLayoutAt, coerceStorageWordAs, Value.forceAbiLazy, Ty.coerceValue?,
    Value.asStorageWord?, norm_lt hv, StorageLayout.clearDepth, bind, Except.bind, pure, Except.pure]

/-- A storage-to-storage copy into a mapping-to-`bool` entry stores through the entry's storage
path the same word `storeIndex_boolMap` stores. -/
theorem storeBase_boolMap {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {x : String} {k : Nat}
    (hk : boolMapOf? E.fields x = some k) {w v : Nat} (hw : w < wordSize) (hv : v ≤ 1)
    (se : Bool) :
    rt.storeStorageBasePathWithDeepClear ctx (.field x) [.word w] (.word v) se =
      .ok { rt with state := rt.state.storeSlot (solHash w k) v } := by
  obtain ⟨f, hf, rfl⟩ := boolMapOf?_spec hrel.fields hk
  have hv' : v = 0 ∨ v = 1 := by omega
  rw [Runtime.storeStorageBasePathWithDeepClear]
  simp only [Runtime.storageMaterializedValue, Runtime.derefMemoryValueDeep,
    Runtime.derefMemoryValueWithFuel, bind, Except.bind, pure, Except.pure]
  rw [resolve_boolMap hf hw]
  cases se <;> rcases hv' with rfl | rfl <;>
  simp [State.storeStorageLayoutAtWithDeepClear, State.storeStorageLayoutAtWithDeepClearFuelMode,
    State.storeStorageLayoutAt, coerceStorageWordAs, Value.forceAbiLazy, Ty.coerceValue?,
    Value.asStorageWord?, StorageLayout.clearDepth, bind, Except.bind, pure, Except.pure, wordEq,
    SolidCore.Solidity.Shared.norm, modulus_eq]

/-- `storePath_map2` with or without sign extension, as a storage-to-storage copy into a nested
mapping's entry stores. -/
theorem storeBase_map2 {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) {x : String} {k : Nat}
    (hk : map2Of? E.fields x = some k) {w1 w2 v : Nat} (h1 : w1 < wordSize) (h2 : w2 < wordSize)
    (hv : v < wordSize) (se : Bool) :
    rt.storeStorageBasePathWithDeepClear ctx (.field x) [.word w1, .word w2] (.word v) se =
      .ok { rt with state := rt.state.storeSlot (solHash w2 (solHash w1 k)) v } := by
  obtain ⟨f, hf, rfl⟩ := map2Of?_spec hrel.fields hk
  rw [Runtime.storeStorageBasePathWithDeepClear]
  simp only [Runtime.storageMaterializedValue, Runtime.derefMemoryValueDeep,
    Runtime.derefMemoryValueWithFuel, bind, Except.bind, pure, Except.pure]
  rw [resolve_map2 hf h1 h2]
  cases se <;>
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
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) {es : List Expr} {gs vs : List WExpr}
    (h : eraseExprs fields S es = some (gs, vs)) :
    Expr.evalList ctx rt es =
      if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
      else .done (.ok (vs.map (fun e => Value.word (e.eval ρ)), rt)) :=
  eval_wordList ρ fields S rt (Expr.evalListFuel · ctx) (Expr.evalFuel · ctx rt)
    (fun _ _ _ => by simp only [Expr.evalListFuel]) (fun _ => by simp only [Expr.evalListFuel])
    (fun n e g v he hn => eval_erase ρ fields ctx rt S hrel e g v n he hn) es gs vs _ h le_rfl


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

theorem assignLocal_word {ρ : Val} {T : Tags} {rt : Runtime} {sc sc' : Scopes} {x : String} {v : WExpr}
    (hfr : rt.locals = sc.map (frameOfT ρ T)) (hx : T.get x = .word) (h : Scopes.set sc x v = some sc') :
    rt.assignLocal? x (.word (v.eval ρ)) = some { rt with locals := sc'.map (frameOfT ρ T) } := by
  obtain ⟨old, hold⟩ := Scopes.get?_of_set h
  have hl : rt.lookupLocal? x = some (.word (old.eval ρ)) := by
    simp [Runtime.lookupLocal?, hfr, envT_lookup, hold, hx]
  simp [Runtime.assignLocal?, hl, Value.coerceLike?, hfr, envT_assign ρ T x v hx sc, h]

theorem assignMany_words {ρ : Val} {T : Tags} : ∀ (xs : List String) (ws : List WExpr) (rt : Runtime)
    (sc sc' : Scopes), rt.locals = sc.map (frameOfT ρ T) → (∀ x ∈ xs, T.get x = .word) →
    Scopes.setMany sc xs ws = some sc' →
    rt.assignNamedValues? xs (ws.map fun e => .word (e.eval ρ)) =
        some { rt with locals := sc'.map (frameOfT ρ T) } ∧
      rt.assignNamedValuesRef? xs (ws.map fun e => .word (e.eval ρ)) =
        some { rt with locals := sc'.map (frameOfT ρ T) }
  | [], [], rt, sc, sc', hfr, _, h => by
    simp only [Scopes.setMany, Option.some.injEq] at h
    subst h
    rw [← hfr]
    exact ⟨rfl, rfl⟩
  | x :: xs, w :: ws, rt, sc, sc', hfr, ht, h => by
    simp only [Scopes.setMany, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨sc1, h1, h2⟩ := h
    have ha := assignLocal_word hfr (ht x List.mem_cons_self) h1
    obtain ⟨ih1, ih2⟩ := assignMany_words xs ws { rt with locals := sc1.map (frameOfT ρ T) } sc1 sc' rfl
      (fun y hy => ht y (List.mem_cons_of_mem _ hy)) h2
    simp only [List.map_cons, Runtime.assignNamedValues?, Runtime.assignNamedValuesRef?,
      Runtime.assignLocalRefAware?, ha]
    exact ⟨ih1, ih2⟩
  | [], _ :: _, _, _, _, _, _, h | _ :: _, [], _, _, _, _, _, h => by simp [Scopes.setMany] at h

theorem eval_refArgs (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) {es : List Expr} {gs vs : List WExpr}
    (h : eraseExprs fields S es = some (gs, vs)) :
    Expr.evalRefArgList ctx rt es =
      if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
      else .done (.ok (vs.map (fun e => Value.word (e.eval ρ)), rt)) :=
  eval_wordList ρ fields S rt (Expr.evalRefArgListFuel · ctx) (fun _ => Expr.evalRefArg ctx rt)
    (fun _ _ _ => by simp only [Expr.evalRefArgListFuel]) (fun _ => by simp only [Expr.evalRefArgListFuel])
    (fun _ e g v he _ => by
      unfold Expr.evalRefArg
      split
      · simp only [(var_refs hrel he).1, (var_refs hrel he).2]; exact eval_eq ρ fields ctx rt S hrel he
      · exact eval_eq ρ fields ctx rt S hrel he)
    es gs vs _ h le_rfl


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

theorem collectRef_words (ρ : Val) (rt : Runtime) (S : SymState)
    (hfr : rt.locals = S.scopes.map (frameOfT ρ S.tags)) : ∀ (rs : List BindingDecl) (ws : List WExpr),
    rs.all wordDecl = true → rs.mapM (fun r => S.word? r.name) = some ws →
    collectReturnBindingsRef.collect rt rs = .ok (ws.map fun e => .word (e.eval ρ))
  | [], ws, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | r :: rs, ws, hr, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hr
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    have hl : rt.lookupLocal? r.name = some (.word (w.eval ρ)) := lookup_word hfr hw
    simp [collectReturnBindingsRef.collect, hl, deref_word', (wordDecl_spec hr.1 _).1,
      collectRef_words ρ rt S hfr rs ws' hr.2 hws', bind, Except.bind, pure, Except.pure]

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
    exact ⟨_, rfl, { hrel1 with frames := hrel.frames, sender := hrel.sender }⟩
  · rename_i ht
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨sc, hsc, rfl⟩ := h
    obtain ⟨hts, hsc⟩ := SymState.setManyW_spec hsc
    have := (assignMany_words targets ws { rt1 with locals := rt.locals } S.scopes sc hrel.frames hts hsc).2
    have hne : targets.isEmpty = false := by cases targets <;> simp_all
    refine ⟨.normal { rt1 with locals := sc.map (frameOfT ρ S.tags) }, ?_,
      (show StmtRel ρ E ctx { rt1 with locals := sc.map (frameOfT ρ S.tags) }
        { scopes := sc, writes := S1.writes, logs := S1.logs, caller := S.caller, tags := S.tags }
        from { hrel1 with frames := rfl, sender := hrel.sender })⟩
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
      collectRef_words ρ rt1 S1 h1.frames fn.returns ws hr hws]
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
        collectRef_words ρ rt1 S1 h1.frames fn.returns ws hr hws]
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
      obtain ⟨hts, hsc⟩ := SymState.setManyW_spec hsc
      have : ((vs.map fun e => Value.word (e.eval ρ)).isEmpty || names.isEmpty) = false := by
        cases vs <;> cases names <;> simp_all
      have ha := (assignMany_words names vs rt1 S1.scopes sc h1.frames hts hsc).1
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

theorem uintCleanup_256_unchecked (w : Nat) (hw : w < wordSize) :
    uintCleanup? false 256 (.word w) = .ok (.word w) := by
  simp [uintCleanup?, Value.forceAbiLazy, Value.asStorageWord?, norm_lt hw, uintCast?, bind,
    Except.bind, Nat.mod_eq_of_lt hw]

theorem apply_add_wrap (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply false .add (.word a) (.word b) = .ok (.word ((a + b) % wordSize)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, norm_lt ha, norm_lt hb,
    bind, Except.bind, Functor.map, Except.map, checkedAdd, addWord_eq]

theorem apply_sub_wrap (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply false .sub (.word a) (.word b) = .ok (.word ((a + (wordSize - b)) % wordSize)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, norm_lt ha, norm_lt hb,
    bind, Except.bind, Functor.map, Except.map, checkedSub, subWord_eq a b ha hb]

theorem apply_ge_unchecked (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply false .ge (.word a) (.word b) = .ok (.word (if a < b then 0 else 1)) := by
  by_cases h : a < b <;>
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, bind, Except.bind, Functor.map,
    Except.map, ltWord_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, boolWord, wordTruthy, h,
    SolidCore.Solidity.Shared.norm, modulus_eq]

theorem apply_le_unchecked (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply false .le (.word a) (.word b) = .ok (.word (if b < a then 0 else 1)) := by
  by_cases h : b < a <;>
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, bind, Except.bind, Functor.map,
    Except.map, gtWord_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, boolWord, wordTruthy, h,
    SolidCore.Solidity.Shared.norm, modulus_eq]

theorem apply_ne_unchecked (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply false .ne (.word a) (.word b) = .ok (.word (if a = b then 0 else 1)) := by
  by_cases h : a = b <;>
  simp [BinaryOp.apply, Value.forceAbiLazy, bind, Except.bind, Functor.map, Except.map, boolWord, wordEq,
    norm_lt ha, norm_lt hb, h]

theorem eval_wrapRead (ρ : Val) (ctx : Context) (rt : Runtime) (S : SymState)
    (hchk : ctx.checked = false)
    (hloc : ∀ x e, S.word? x = some e → rt.lookupLocal? x = some (.word (e.eval ρ))) :
    ∀ (e : Expr) (w : WExpr) (fuel : Nat), wrapRead S e = some w → Expr.orderFuel e < fuel →
      Expr.evalFuel fuel ctx rt e = .done (.ok (.word (w.eval ρ), rt)) := by
  intro e w fuel h hf
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  cases e
  case var x =>
    simp only [wrapRead] at h
    have hl := hloc x w h
    simp [Expr.evalFuel, Runtime.lookupStorageBase?, hl, Runtime.derefMemoryValue]
    rfl
  case castOp k b e =>
    cases k
    case uintCleanup =>
      by_cases hb : b = 256
      · subst hb
        simp only [wrapRead] at h
        have ih := eval_wrapRead ρ ctx rt S hchk hloc e w n h (by simp [Expr.orderFuel] at hf; omega)
        simp only [Expr.evalFuel, ih, hchk]
        simp only [bind, EvmCompiler.Simulation.Interaction.bind, liftM, monadLift,
          MonadLift.monadLift, uintCleanup_256_unchecked _ (w.eval_lt ρ), SolI.ofExcept]
        rfl
      · simp [wrapRead, hb] at h
    all_goals simp [wrapRead] at h
  case binary op l r =>
    cases hl : wrapRead S l with
    | none => simp [wrapRead, hl] at h
    | some vl =>
    cases hr : wrapRead S r with
    | none => simp [wrapRead, hl, hr] at h
    | some vr =>
    have ihl := eval_wrapRead ρ ctx rt S hchk hloc l vl n hl (by simp [Expr.orderFuel] at hf; omega)
    have ihr := eval_wrapRead ρ ctx rt S hchk hloc r vr n hr (by simp [Expr.orderFuel] at hf; omega)
    have hal := vl.eval_lt ρ
    have har := vr.eval_lt ρ
    cases op <;> simp only [wrapRead, wrapOf, hl, hr, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, reduceCtorEq, Option.bind_none] at h
    all_goals
      subst h
      simp only [Expr.evalFuel, ihr, ihl, hchk]
      simp only [pure, EvmCompiler.Simulation.Interaction.pure, bind,
        EvmCompiler.Simulation.Interaction.bind, liftM, monadLift, MonadLift.monadLift, ihl, ihr,
        apply_add_wrap _ _ hal har, apply_sub_wrap _ _ hal har, SolI.ofExcept]
      simp [WExpr.eval, BinOp.eval, Nat.mod_mod]
  all_goals simp [wrapRead] at h

/-- A `require` whose condition gives the word `v` goes on when `v` is not zero, and reverts with
its reason otherwise. -/
theorem eval_require {ρ : Val} {E : EraseEnv} {ctx ctx' : Context} {rt rt' : Runtime}
    {S : SymState} (hrel : StmtRel ρ E ctx rt' S) {n : Nat} {tbl : FunctionTable} {c : Expr}
    {rs : Option String} {v : WExpr}
    (hc : (Expr.eval ctx' rt c).caught = .done (.ok (.ok (.word (v.eval ρ), rt')))) :
    ∃ r, Stmt.eval (n + 1) tbl ctx' rt (.requireStmt c rs) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((Br.ite v (.leaf (.normal S)) (.leaf (.reverted (failOf rs)))).eval ρ) := by
  rw [Stmt.eval]
  simp only [hc, bind_done_ok, Value.expectWord, norm_lt (v.eval_lt ρ), Br.eval, wordTruthy]
  by_cases hv : v.eval ρ = 0
  · refine ⟨.reverted rt' (failOf rs).data, ?_, by simp only [hv, ↓reduceIte, LeafRel]⟩
    cases rs <;> simp [hv] <;> rfl
  · refine ⟨.normal rt', ?_, by simp only [hv, ↓reduceIte, LeafRel]; exact hrel⟩
    simp [hv, SolidCore.Solidity.Shared.norm, modulus_eq, Nat.mod_eq_of_lt (v.eval_lt ρ)]
    rfl

theorem eval_uncheckedCond (ρ : Val) (ctx : Context) (rt : Runtime) (S : SymState)
    (hchk : ctx.checked = false) (hframes : rt.locals = S.scopes.map (frameOfT ρ S.tags))
    (hloc : ∀ x e, S.word? x = some e → rt.lookupLocal? x = some (.word (e.eval ρ)))
    {c : Expr} {z : String} {w v : WExpr} {L : Scopes}
    (h : uncheckedCond S c = some (z, w, v)) (hL' : S.setW z w = some L) :
    ∀ fuel, Expr.orderFuel c < fuel →
      Expr.evalFuel fuel ctx rt c = .done (.ok (.word (v.eval ρ), { rt with locals := L.map (frameOfT ρ S.tags) })) := by
  obtain ⟨hz, hL⟩ := SymState.setW_spec hL'
  intro fuel hf
  unfold uncheckedCond at h
  split at h
  case h_2 => simp at h
  rename_i cmp z' rhs c2
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨vc, hc, w', hw, v', ho, rfl, rfl, rfl⟩ := h
  obtain ⟨old, hold⟩ := Scopes.get?_of_set hL
  have hx := hloc z' old (by simp [SymState.word?, hz, hold])
  have hbase : rt.lookupStorageBase? z' = none := by simp [Runtime.lookupStorageBase?, hx]
  have hassign : rt.assignLocal? z' (.word (w'.eval ρ)) =
      some { rt with locals := L.map (frameOfT ρ S.tags) } :=
    assignLocal_word hframes hz hL
  simp only [Expr.orderFuel] at hf
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hvc := eval_wrapRead ρ ctx rt S hchk hloc c2 vc (j + 1 + 1 + 1) hc (by omega)
  have hvw := eval_wrapRead ρ ctx rt S hchk hloc rhs w' (j + 1) hw (by omega)
  have hres : Expr.resolveLValueFuel (j + 1) ctx rt (.var z') = .done (.ok (.local z', rt)) := by
    simp [Expr.resolveLValueFuel, hbase, hx]
    rfl
  have hwv := w'.eval_lt ρ
  have hcv := vc.eval_lt ρ
  have hA : Expr.evalFuel (j + 1 + 1) ctx rt (.assignment none none (.var z') rhs) =
      .done (.ok (.word (w'.eval ρ), { rt with locals := L.map (frameOfT ρ S.tags) })) := by
    rw [Expr.evalFuel]
    simp only [pure, EvmCompiler.Simulation.Interaction.pure, bind,
      EvmCompiler.Simulation.Interaction.bind, liftM, monadLift, MonadLift.monadLift, hvw, hres,
      ResolvedLValue.write, hassign, SolI.ofExcept]
  have hC : Expr.evalFuel (j + 1 + 1 + 1) ctx rt
      (.castOp .uintCleanup 256 (.assignment none none (.var z') rhs)) =
      .done (.ok (.word (w'.eval ρ), { rt with locals := L.map (frameOfT ρ S.tags) })) := by
    rw [Expr.evalFuel]
    simp only [pure, EvmCompiler.Simulation.Interaction.pure, bind,
      EvmCompiler.Simulation.Interaction.bind, liftM, monadLift, MonadLift.monadLift, hA, hchk,
      uintCleanup_256_unchecked _ hwv, SolI.ofExcept]
  cases cmp <;> simp [cmpOf] at ho
  all_goals
    subst ho
    rw [Expr.evalFuel] <;> try (intro h; cases h)
    simp only [pure, EvmCompiler.Simulation.Interaction.pure, bind,
      EvmCompiler.Simulation.Interaction.bind, liftM, monadLift, MonadLift.monadLift, hvc, hC, hchk,
      SolI.ofExcept, apply_ge_unchecked _ _ hwv hcv, apply_le_unchecked _ _ hwv hcv,
      apply_ne_unchecked _ _ hwv hcv]
    simp only [WExpr.eval, BinOp.eval, UnOp.eval]
    split <;> simp_all

theorem eval_unchecked (ρ : Val) (E : EraseEnv) (ctx : Context) (k : Nat) (body : Stmt)
    (S : SymState) (b : Br) (h : eraseUnchecked S body = some b) (rt : Runtime)
    (hrel : StmtRel ρ E ctx rt S) :
    ∃ r, Stmt.eval (k + 2) E.tbl { ctx with checked := false } rt body = .done (.ok r) ∧
      LeafRel ρ E ctx r (b.eval ρ) := by
  unfold eraseUnchecked at h
  split at h
  case h_2 => simp at h
  rename_i c rs
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨⟨z, w, v⟩, hc, L, hL, rfl⟩ := h
  have hrel' := hrel.pushScope
  have hcond : Expr.eval { ctx with checked := false } rt.pushScope c =
      .done (.ok (.word (v.eval ρ), { rt.pushScope with locals := L.map (frameOfT ρ S.tags) })) :=
    eval_uncheckedCond ρ _ rt.pushScope S.push rfl hrel'.frames
      (fun x e he => hrel'.expr.locals x e he) hc hL _ (Nat.lt_succ_self _)
  obtain ⟨r, hr, hl⟩ := eval_require (n := k) (tbl := E.tbl) (rs := rs)
    (show StmtRel ρ E ctx { rt.pushScope with locals := L.map (frameOfT ρ S.tags) } { S.push with scopes := L }
      from { hrel' with frames := rfl }) (by rw [hcond]; rfl)
  refine ⟨r.mapRuntime Runtime.popScope, ?_, ?_⟩
  · rw [Stmt.eval]
    simp only [Stmt.evalList]
    rw [hr, bind_done_ok]
    cases r <;> rfl
  · rw [Br.eval_mapS]
    exact hl.popScope

/-- An assignment is never an expression of the fragment: `eraseStmt` erases the assignments it
knows by their own cases, and its expression statement of an assignment erases to nothing. -/
@[simp] theorem eraseExpr_assignment (fields : List StorageField) (S : SymState) (op? : Option BinaryOp)
    (cleanup? : Option ValueCleanup) (target rhs : Expr) :
    eraseExpr fields S (.assignment op? cleanup? target rhs) = none := by
  simp [eraseExpr]

/-- An expression statement of the fragment (`y;`, an expression whose value is dropped): SolidCore
evaluates the expression and goes on with the runtime it leaves, which the expression's erasure
keeps, or reverts with `Panic(0x11)` when one of its overflow conditions holds. -/
theorem eval_exprStmt (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (n : Nat) (hrel : StmtRel ρ E ctx rt S) {e : Expr} {gs : List WExpr} {v : WExpr}
    (he : eraseExpr E.fields S e = some (gs, v)) :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt (.exprStmt e) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((guards gs (.leaf (.normal S))).eval ρ) := by
  have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
  rw [Stmt.eval]
  simp only [heval, caught_exprResult, guards_eval]
  guard_cases hg : gs.any (fun g => g.eval ρ != 0)
  exact ⟨.normal rt, rfl, hrel⟩

/-- An increment or decrement is never an expression of the fragment: `eraseStmt` erases the
statements of one it knows by their own cases. -/
@[simp] theorem eraseExpr_incDec (fields : List StorageField) (S : SymState) (op : BinaryOp)
    (ret : Bool) (cleanup? : Option ValueCleanup) (target : Expr) :
    eraseExpr fields S (.incDec op ret cleanup? target) = none := by
  simp [eraseExpr]

/-- An increment or decrement statement `target++` (or `--target`, its value dropped) with a
`uint b` cleanup, whose target resolves to `lv` after the overflow conditions `gi` and holds the
word `cur`: the target's overflow conditions, the operation's with the word 1 and the cleanup's
range check, then the write of the new word, which `wr` and `S'` relate. SolidCore reads the
target, adds or subtracts its type's one and writes the cleaned word, as `target op= 1` does. -/
theorem eval_incDec (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) (S : SymState)
    (hrel : StmtRel ρ E ctx rt S) (n : Nat) {op : BinaryOp} {ret : Bool} {b : Nat} {target : Expr}
    {gi cg : List WExpr} {cur : WExpr} {o : BinOp} {lv : ResolvedLValue}
    {wr : WExpr → Runtime} {S' : WExpr → SymState}
    (hres : ∀ F, target.orderFuel < F → Expr.resolveLValueFuel F ctx rt target =
      if gi.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
      else .done (.ok (lv, rt)))
    (ho : binOf op = some o) (hcg : cleanupGuard b (.bin o cur (.lit 1)) = some cg)
    (hrd : lv.read ctx rt = .ok (.word (cur.eval ρ)))
    (hwr : ∀ w : WExpr, lv.write ctx rt (.word (w.eval ρ)) = .ok (wr w))
    (hrelw : ∀ w, StmtRel ρ E ctx (wr w) (S' w)) :
    ∃ r, Stmt.eval (n + 1) E.tbl ctx rt
        (.exprStmt (.incDec op ret (some (.uint b)) target)) = .done (.ok r) ∧
      LeafRel ρ E ctx r ((guards (gi ++ (overflow o cur (.lit 1)).toList ++ cg)
        (.leaf (.normal (S' (.bin o cur (.lit 1)))))).eval ρ) := by
  obtain ⟨hb0, hb, hcgv⟩ := cleanupGuard_spec ρ hcg
  have hcl : ValueCleanup.apply true (.uint b) (.word ((WExpr.bin o cur (.lit 1)).eval ρ)) =
      if (WExpr.bin o cur (.lit 1)).eval ρ < 2 ^ b then .ok (.word ((WExpr.bin o cur (.lit 1)).eval ρ))
      else .error (.panic 0x11) := uintCleanup_lt _ _ (WExpr.eval_lt ρ _) hb0 hb
  have hone : Value.word 1 = Value.word ((WExpr.lit 1).eval ρ) := by
    simp [WExpr.eval, wordSize]
  have happ := apply_erased ρ ho cur (.lit 1)
  rw [← hone] at happ
  rw [Stmt.eval]
  simp only [Expr.eval, Expr.orderFuel]
  rw [Expr.evalFuel, hres _ (by omega), guards_eval]
  simp only [any_append]
  guard_cases hgi : gi.any (fun g => g.eval ρ != 0)
  rw [bind_done_ok]
  simp only [ResolvedLValue.applyIncDecCleanup, hrel.checked, liftM, monadLift,
    MonadLift.monadLift, SolI.ofExcept, bind, Except.bind]
  rw [hrd]
  dsimp only [Value.oneLike?]
  rw [happ, hcgv]
  guard_cases ho' : (overflow o cur (.lit 1)).toList.any (fun g => g.eval ρ != 0)
  rw [hcl]
  by_cases hc : (WExpr.bin o cur (.lit 1)).eval ρ < 2 ^ b
  · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwr]
    cases ret <;> exact ⟨_, rfl, hrelw _⟩
  · simp only [hc, decide_false, Bool.not_false, ↓reduceIte]
    exact ⟨_, rfl, rfl⟩

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
      rename_i hty'
      have hty := hty'.1
      have hxw := hty'.2
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
              (S.scopes.declare x (.lit 0)).map (frameOfT ρ S.tags) := by
            rw [Runtime.declareLocal, hrel.frames]
            exact envT_declare ρ S.tags S.scopes x (.lit 0) hxw
          exact { hrel with frames := hf }
      | some e =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨gs, v⟩, he, rfl⟩ := h
        have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
        rw [Stmt.eval]
        simp only [heval, caught_exprResult, guards_eval]
        guard_cases hg : gs.any (fun g => g.eval ρ != 0)
        simp only [bind_done_ok, hco]
        refine ⟨.normal (rt.declareLocal x (.word (v.eval ρ))), rfl, ?_⟩
        have hf : (rt.declareLocal x (.word (v.eval ρ))).locals =
            (S.scopes.declare x v).map (frameOfT ρ S.tags) := by
          rw [Runtime.declareLocal, hrel.frames, envT_declare ρ S.tags S.scopes x v hxw]
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
      have hlist := eval_exprList ρ E.fields ctx rt S hrel.expr hes
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
      rw [heq, hlist]
      rw [guards_eval]
      guard_cases hg : gs.any (fun g => g.eval ρ != 0)
      simp only [caught_done_ok, bind_done_ok, unschedule_map, materialize_words]
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
      have hev := eval_refArgs ρ E.fields ctx rt S hrel.expr hargs
      rw [Stmt.eval]
      simp only [hev]
      rw [guards_eval]
      guard_cases hg : gs.any (fun g => g.eval ρ != 0)
      simp only [caught_done_ok, bind_done_ok, hfn, internalCallEnter?,
        initialFrame_words ρ fn vs hp hr hvl]
      have hctx : ({ ctx with checked := true } : Context) = ctx := by
        rw [show true = ctx.checked from hrel.checked.symm]
      have hrel0 : StmtRel ρ E ctx { rt with locals := [frameOf ρ (callFrame fn vs)] }
          { scopes := [callFrame fn vs], writes := S.writes, logs := S.logs, caller := S.caller } :=
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
      rw [guards_eval]
      by_cases hg : gs.any (fun g => g.eval ρ != 0) = true
      · rw [Stmt.eval]
        simp only [heval, caught_exprResult, hg, ↓reduceIte]
        exact ⟨_, rfl, rfl⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
        exact eval_require hrel (by simp only [heval, caught_exprResult, hg, Bool.false_eq_true, ↓reduceIte])
    case revertError r =>
      simp only [eraseStmt, Option.some.injEq] at h
      subst h
      exact ⟨.reverted rt (failOf r).data, by cases r <;> (rw [Stmt.eval]; rfl), rfl⟩

    case assign target e =>
      cases target
      case var x =>
        simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨gs, v⟩, he, L', hL', rfl⟩ := h
        obtain ⟨hxw, hL⟩ := SymState.setW_spec hL'
        obtain ⟨old, hold⟩ := Scopes.get?_of_set hL
        have hx : rt.lookupLocal? x = some (.word (old.eval ρ)) :=
          hrel.expr.locals x old (by simp [SymState.word?, hxw, hold])
        have hmem : rt.lookupMemoryRef? x = none := by simp [Runtime.lookupMemoryRef?, hx]
        have hbase : rt.lookupStorageBase? x = none := by simp [Runtime.lookupStorageBase?, hx]
        have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
        have hres : LValue.resolveWithRuntime (.var x) ctx rt = .done (.ok (.local x, rt)) := by
          simp [LValue.resolveWithRuntime, Expr.resolveLValue, LValue.toExpr, Expr.orderFuel,
            Expr.resolveLValueFuel, hbase, hx]
          rfl
        have hassign : rt.assignLocal? x (.word (v.eval ρ)) =
            some { rt with locals := L'.map (frameOfT ρ S.tags) } :=
          assignLocal_word hrel.frames hxw hL
        have hrel' : StmtRel ρ E ctx { rt with locals := L'.map (frameOfT ρ S.tags) }
            { S with scopes := L' } := { hrel with frames := rfl }
        rw [Stmt.eval]
        simp only [LValue.wantsMemoryRefRhs, hmem, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte, heval, caught_exprResult]
        rw [guards_eval]
        guard_cases hg : gs.any (fun g => g.eval ρ != 0)
        refine ⟨.normal { rt with locals := L'.map (frameOfT ρ S.tags) }, ?_, hrel'⟩
        split
        · split
          · simp_all
          · simp only [bind_done_ok, hres, caught_done_ok, ite_self, ResolvedLValue.write, hassign,
              ResolvedLValue.asStoragePath?]
            rfl
        · simp only [bind_done_ok, hres, caught_done_ok, ite_self, ResolvedLValue.write, hassign,
            ResolvedLValue.asStoragePath?]
          rfl
      case storageIndex x i =>
        simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨gs, v⟩, he, ⟨gi, key⟩, hi, h⟩ := h
        obtain ⟨k, hk, hst, hcp, rfl⟩ : ∃ k, k < wordSize ∧
            rt.storeStorageIndexWithDeepClear ctx x (.word (key.eval ρ)) (.word (v.eval ρ)) =
              .ok { rt with state := rt.state.storeSlot (solHash (key.eval ρ) k) (v.eval ρ) } ∧
            rt.storeStorageBasePathWithDeepClear ctx (.field x) [.word (key.eval ρ)]
                (.word (v.eval ρ)) false =
              .ok { rt with state := rt.state.storeSlot (solHash (key.eval ρ) k) (v.eval ρ) } ∧
            b = guards (gs ++ gi)
              (.leaf (.normal { S with writes := S.writes.set (.hash key (.lit k)) v })) := by
          split at h
          · rename_i k hk
            simp only [Option.some.injEq] at h
            obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk
            exact ⟨f.slot, hf.slot, storeIndex_map hrel hk (key.eval_lt ρ) (v.eval_lt ρ),
              storeBase_map hrel hk (key.eval_lt ρ) (v.eval_lt ρ) false, h.symm⟩
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨k, hk, h⟩ := h
            split at h
            · rename_i hb
              simp only [Option.some.injEq] at h
              obtain ⟨f, hf, rfl⟩ := boolMapOf?_spec hrel.fields hk
              exact ⟨f.slot, hf.slot, storeIndex_boolMap hrel hk (key.eval_lt ρ)
                (Nat.le_trans (bound_sound hrel.facts v) hb),
                storeBase_boolMap hrel hk (key.eval_lt ρ)
                  (Nat.le_trans (bound_sound hrel.facts v) hb) false, h.symm⟩
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
        guard_cases hg : gs.any (fun g => g.eval ρ != 0)
        simp only [bind_done_ok, hres]
        guard_cases hgi : gi.any (fun g => g.eval ρ != 0)
        simp only [bind_done_ok, ResolvedLValue.write, ResolvedLValue.asStoragePath?, hst, hcp,
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
          have hcp := storeBase_map2 hrel hk (k1.eval_lt ρ) (k2.eval_lt ρ) (v.eval_lt ρ) false
          rw [Stmt.eval]
          simp only [LValue.wantsMemoryRefRhs, LValue.toExpr, Expr.hasStorageRoot, Bool.true_or,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval, caught_exprResult]
          rw [guards_eval]
          simp only [any_append]
          guard_cases hg : gs.any (fun g => g.eval ρ != 0)
          simp only [bind_done_ok, hres]
          guard_cases hgi : (g1.any (fun g => g.eval ρ != 0) || g2.any (fun g => g.eval ρ != 0))
          simp only [bind_done_ok, ResolvedLValue.write, ResolvedLValue.asStoragePath?, hst, hcp,
            ite_self]
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
        rw [Stmt.eval]
        simp only [LValue.wantsMemoryRefRhs, Bool.false_eq_true, ↓reduceIte, heval, caught_exprResult]
        rw [guards_eval]
        guard_cases hg : gs.any (fun g => g.eval ρ != 0)
        refine ⟨.normal _, ?_, hrel.writeField hfx v⟩
        simp only [bind_done_ok, hres, caught_done_ok, ResolvedLValue.write, (hrel.field_rw hfx).2 v,
          ite_self]
        rfl
      all_goals simp [eraseStmt] at h
    case returnValues es =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨gs, vs⟩, hes, rfl⟩ := h
      have hl := eval_returnList ρ E.fields ctx rt S hrel.expr hes
      rw [Stmt.eval]
      simp only [hl, guards_eval]
      guard_cases hg : gs.any (fun g => g.eval ρ != 0)
      exact ⟨.returned rt (vs.map fun e => Value.word (e.eval ρ)), rfl, hrel, rfl⟩
    case ifElse c t e =>
      simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨gs, v⟩, hc, bt, hbt, be, hbe, rfl⟩ := h
      have heval := eval_eq ρ E.fields ctx rt S hrel.expr hc
      rw [Stmt.eval]
      simp only [heval, caught_exprResult, guards_eval]
      guard_cases hg : gs.any (fun g => g.eval ρ != 0)
      simp only [bind_done_ok, Value.expectWord, norm_lt (v.eval_lt ρ), Br.eval, wordTruthy]
      by_cases hv : v.eval ρ = 0
      · obtain ⟨r, hr, hl⟩ := ih e S be hbe rt hrel
        refine ⟨r, ?_, by simpa [hv] using hl⟩
        simp [hv, hr]
      · obtain ⟨r, hr, hl⟩ := ih t S bt hbt rt hrel
        refine ⟨r, ?_, by simpa [hv] using hl⟩
        simp [hv, hr]
    case exprStmt ex =>
      cases ex
      case incDec op ret cleanup? target =>
        rcases cleanup? with _ | c
        · simp [eraseStmt] at h
        cases c
        all_goals first | (simp [eraseStmt] at h; done) | skip
        rename_i b
        cases target
        all_goals first | (simp [eraseStmt] at h; done) | skip
        rename_i m x idx
        cases m <;> cases idx
        all_goals first | (simp [eraseStmt] at h; done) | skip
        simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨k, off, bytes⟩, hk, o, ho, cg, hcg, rfl⟩ := h
        obtain ⟨f, hfx, rfl, rfl, rfl⟩ := fieldOf?_spec hrel.fields hk
        obtain ⟨hread, hst⟩ := hrel.field_rw hfx
        simpa only [List.nil_append] using eval_incDec ρ E ctx rt S hrel n (gi := []) (ret := ret)
          (S' := fun w => { S with
            writes := S.writes.set (.lit f.slot)
              (writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes) })
          (fun F hF => by
            obtain ⟨m, rfl⟩ : ∃ m, F = m + 1 := ⟨F - 1, by omega⟩
            simp [Expr.resolveLValueFuel] <;> rfl)
          ho hcg hread (fun w => hst w _) (fun w => hrel.writeField hfx w)
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
          obtain ⟨hread, hst⟩ := hrel.field_rw hfx
          cases op? <;> cases cleanup? <;> simp only [Option.some.injEq, reduceCtorEq] at h
          case none.none =>
            subst h
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
            rw [guards_eval]
            guard_cases hg : gs.any (fun g => g.eval ρ != 0)
            simp only [ResolvedLValue.write, hst v]
            exact ⟨_, rfl, hrel.writeField hfx v⟩
          case some.some op c =>
            cases c <;> simp only [reduceCtorEq] at h
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨o, ho, cg, hcg, rfl⟩ := h
            simpa only [List.append_nil] using eval_compound ρ E ctx rt S hrel n (gi := [])
              (S' := fun w => { S with
                writes := S.writes.set (.lit f.slot)
                  (writeField (S.writes.read (.lit f.slot)) w f.packedOffset f.packedBytes) })
              hv (fun F hF => by
                obtain ⟨m, rfl⟩ : ∃ m, F = m + 1 := ⟨F - 1, by omega⟩
                simp [Expr.resolveLValueFuel] <;> rfl)
              ho hcg hread (fun w => hst w _) (fun w => hrel.writeField hfx w)
        all_goals simp [eraseStmt, eraseExpr] at h
        all_goals simp [eraseStmt, eraseExpr] at h
      all_goals
        simp only [eraseStmt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨gs, v⟩, he, rfl⟩ := h
        exact eval_exprStmt ρ E ctx rt S n hrel he
    case unchecked body =>
      simp only [eraseStmt] at h
      split at h
      case isFalse => simp at h
      rename_i hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      obtain ⟨r, hr, hl⟩ := eval_unchecked ρ E ctx k body S b h rt hrel
      exact ⟨r, by rw [Stmt.eval]; exact hr, hl⟩
    all_goals simp [eraseStmt] at h


end SolidCore.Refinement.Generic

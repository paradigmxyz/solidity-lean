import Verify.LoopSource.Proof.LoopErased
import SolidCore.Refinement.Generic.LoopRun

/-!
# Erasure of counted loops, and `BodyRuns` of a body with a loop

`eraseStmt` has no loop case, so `bodyRuns_of_erase` gives `BodyRuns` only of loop-free bodies.
`eraseLoopStmt` extends the erasure to `for` statements of one shape: a **counted loop**, whose
every iteration (body, then update) ends normally or reverts with `Panic(0x11)`, adds one to some of
the words it changes (the counter among them) and leaves every other word as it was, and whose
condition is `counter < bound` with a bound the iteration does not change. The driver emits
`for (uint256 i = 0; i < n; i++) { count++; }` in this shape. The erased loop is a closed form:
with `N` the number of iterations (`bound - i` when `i < bound`, else `0`), every word the
iteration adds one to ends `N` higher, and the loop reverts with `Panic(0x11)` exactly when one of
the checked additions overflows, that is when `word + N` wraps for a word with an overflow check.

Nothing about the loop is trusted. The erasure computes a **header**: the state before the loop
with a fresh argument word (`.arg (base + j)`, above every argument word the state and the facts
mention) for every local and for every constant storage slot the iteration writes. It erases the
body and the update at the header (`eraseInc`: the generic erasure with `x++` on a local and on a
storage word, which `eraseStmt` has no arm for), and **checks syntactically** that the iteration's
state is the header with each fresh word `w` replaced by `w + 1` or by itself (`instS`), that each
overflow guard is the guard of a word that steps, and that the condition is `counter < bound`.
`eval_accelFor` turns those checks into the obligations of `ForObl` (`LoopErased.lean`): the
invariant is "the header at iteration `t`, no overflow so far", the measure is `N - t`, and the
kernel proves them for every valuation. The loop's fuel is `2 ^ 256 + 1` more than its body's,
since `N < 2 ^ 256`.

* `eraseLoopStmt E fuel s S`: blocks (with their statements erased by `eraseLoopStmt`), counted
  `for` loops, and every statement `eraseInc` erases.
* `bodyRuns_of_eraseLoop`: `eraseLoopStmt E fuel fn.body (initState fn) = some b` gives
  `BodyRuns E fuel fn b`, the premise `hb` of `Verify.LoopSource.Equiv.loop_stage`.

Outside the shape the erasure is `none`: `while` loops, nested loops (the body and update are
erased by `eraseInc`, which has no loop case), bodies that branch other than to `Panic(0x11)`,
`break`/`continue`, returns or reverts in the body, iterations that change a word other than by
`+ 1`, write a computed slot or emit a log, and conditions other than `counter < bound`.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source SolidCore.Refinement.Generic

/-! ## Fresh words and their instantiation -/

/-- `ρ` with its argument words from `base` on replaced by the `len` words `f 0, …, f (len - 1)`. -/
def extV (ρ : Val) (base len : Nat) (f : Nat → Nat) : Val :=
  { ρ with args := (List.range base).map (fun i => ρ.args.getD i 0) ++ (List.range len).map f }

theorem extV_getD (ρ : Val) (base len : Nat) (f : Nat → Nat) (i : Nat) :
    (extV ρ base len f).args.getD i 0 =
      if i < base then ρ.args.getD i 0 else if i - base < len then f (i - base) else 0 := by
  simp only [extV, List.getD_eq_getElem?_getD]
  by_cases h : i < base
  · rw [ite_eq_left h, List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [ite_eq_right h, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range, List.getElem?_map]
    by_cases h2 : i - base < len <;> simp [h2]

theorem extV_congr (ρ : Val) (base len : Nat) {f g : Nat → Nat} (h : ∀ j, j < len → f j = g j) :
    extV ρ base len f = extV ρ base len g := by
  unfold extV
  rw [List.map_congr_left (fun j hj => h j (List.mem_range.mp hj))]

theorem extV_extV (ρ : Val) (base len : Nat) (f g : Nat → Nat) :
    extV (extV ρ base len f) base len g = extV ρ base len g := by
  have : (List.range base).map (fun i => (extV ρ base len f).args.getD i 0) =
      (List.range base).map (fun i => ρ.args.getD i 0) := by
    apply List.map_congr_left
    intro i hi
    rw [extV_getD, ite_eq_left (List.mem_range.mp hi)]
  unfold extV at *
  simp only at this ⊢
  rw [this]


/-- Replace the argument words from `base` on: `.arg (base + j)` becomes `θ j` for `j < len`, and
`0` above. -/
def instW (base len : Nat) (θ : Nat → WExpr) : WExpr → WExpr
  | .lit n => .lit n
  | .arg i => if i < base then .arg i else if i - base < len then θ (i - base) else .lit 0
  | .init k => .init k
  | .un op a => .un op (instW base len θ a)
  | .bin op a b => .bin op (instW base len θ a) (instW base len θ b)
  | .sinit k => .sinit (instW base len θ k)
  | .sel c a b => .sel (instW base len θ c) (instW base len θ a) (instW base len θ b)
  | .hash a b => .hash (instW base len θ a) (instW base len θ b)
  | .caller => .caller

/-- **Instantiating is evaluating at the extended valuation.** -/
theorem eval_instW (ρ : Val) (base len : Nat) (θ : Nat → WExpr) : ∀ e : WExpr,
    (instW base len θ e).eval ρ = e.eval (extV ρ base len fun j => (θ j).eval ρ)
  | .lit _ => rfl
  | .arg i => by
    simp only [instW, WExpr.eval, extV_getD]
    by_cases h : i < base
    · simp [h, WExpr.eval]
    · by_cases h2 : i - base < len
      · simp [h, h2, Nat.mod_eq_of_lt (WExpr.eval_lt ρ _)]
      · simp [h, h2, WExpr.eval]
  | .init _ => rfl
  | .un op a => by simp only [instW, WExpr.eval, eval_instW ρ base len θ a]
  | .bin op a b => by
    simp only [instW, WExpr.eval, eval_instW ρ base len θ a, eval_instW ρ base len θ b]
  | .sinit k => by simp only [instW, WExpr.eval, eval_instW ρ base len θ k]; rfl
  | .sel c a b => by
    simp only [instW, WExpr.eval, eval_instW ρ base len θ c, eval_instW ρ base len θ a,
      eval_instW ρ base len θ b]
  | .hash a b => by
    simp only [instW, WExpr.eval, eval_instW ρ base len θ a, eval_instW ρ base len θ b]; rfl
  | .caller => rfl

/-- Every argument word of `e` is below `base`. -/
def belowW (base : Nat) : WExpr → Bool
  | .lit _ => true
  | .arg i => decide (i < base)
  | .init _ => true
  | .un _ a => belowW base a
  | .bin _ a b => belowW base a && belowW base b
  | .sinit k => belowW base k
  | .sel c a b => belowW base c && belowW base a && belowW base b
  | .hash a b => belowW base a && belowW base b
  | .caller => true

theorem eval_extV_below (ρ : Val) (base len : Nat) (f : Nat → Nat) : ∀ e : WExpr,
    belowW base e = true → e.eval (extV ρ base len f) = e.eval ρ
  | .lit _, _ => rfl
  | .arg i, h => by
    simp only [belowW, decide_eq_true_eq] at h
    simp only [WExpr.eval, extV_getD, ite_eq_left h]
  | .init _, _ => rfl
  | .un op a, h => by
    simp only [belowW] at h
    simp only [WExpr.eval, eval_extV_below ρ base len f a h]
  | .bin op a b, h => by
    simp only [belowW, Bool.and_eq_true] at h
    simp only [WExpr.eval, eval_extV_below ρ base len f a h.1, eval_extV_below ρ base len f b h.2]
  | .sinit k, h => by
    simp only [belowW] at h
    simp only [WExpr.eval, eval_extV_below ρ base len f k h]; rfl
  | .sel c a b, h => by
    simp only [belowW, Bool.and_eq_true] at h
    simp only [WExpr.eval, eval_extV_below ρ base len f c h.1.1, eval_extV_below ρ base len f a h.1.2,
      eval_extV_below ρ base len f b h.2]
  | .hash a b, h => by
    simp only [belowW, Bool.and_eq_true] at h
    simp only [WExpr.eval, eval_extV_below ρ base len f a h.1, eval_extV_below ρ base len f b h.2]; rfl
  | .caller, _ => rfl

/-- One more than the largest argument word `e` mentions (`0` when none). -/
def maxArgW : WExpr → Nat
  | .lit _ => 0
  | .arg i => i + 1
  | .init _ => 0
  | .un _ a => maxArgW a
  | .bin _ a b => max (maxArgW a) (maxArgW b)
  | .sinit k => maxArgW k
  | .sel c a b => max (maxArgW c) (max (maxArgW a) (maxArgW b))
  | .hash a b => max (maxArgW a) (maxArgW b)
  | .caller => 0

/-! ### Bytes, logs, writes and states -/

def instO (base len : Nat) (θ : Nat → WExpr) : OByte → OByte
  | .lit b => .lit b
  | .byteOf e i => .byteOf (instW base len θ e) i

def belowO (base : Nat) : OByte → Bool
  | .lit _ => true
  | .byteOf e _ => belowW base e

def instLog (base len : Nat) (θ : Nat → WExpr) (l : Log) : Log :=
  ⟨l.topics.map (instW base len θ), l.data.map (instO base len θ)⟩

def belowLog (base : Nat) (l : Log) : Bool := l.topics.all (belowW base) && l.data.all (belowO base)

def instWs (base len : Nat) (θ : Nat → WExpr) (ws : Writes) : Writes :=
  ws.map fun p => (instW base len θ p.1, instW base len θ p.2)

def belowWs (base : Nat) (ws : Writes) : Bool := ws.all fun p => belowW base p.1 && belowW base p.2

def instL (base len : Nat) (θ : Nat → WExpr) (L : Locals) : Locals :=
  L.map fun p => (p.1, instW base len θ p.2)

/-- A symbolic state with its fresh words instantiated. -/
def instS (base len : Nat) (θ : Nat → WExpr) (S : SymState) : SymState :=
  { scopes := S.scopes.map (instL base len θ)
    writes := instWs base len θ S.writes
    logs := S.logs.map (instLog base len θ)
    caller := instW base len θ S.caller
    tags := S.tags
    mem := S.mem.map fun p => (p.1, p.2.map (instW base len θ))
    next := S.next }

/-- Every argument word of the state is below `base`. -/
def belowS (base : Nat) (S : SymState) : Bool :=
  S.scopes.all (fun L => L.all fun p => belowW base p.2) && belowWs base S.writes &&
    S.logs.all (belowLog base) && belowW base S.caller

/-- Every argument word of the facts is below `base`. -/
def factsBelow (base : Nat) (K : Facts) : Bool := K.all fun p => belowW base p.1

def maxArgO : OByte → Nat
  | .lit _ => 0
  | .byteOf e _ => maxArgW e

def maxArgList {α : Type} (f : α → Nat) (xs : List α) : Nat := xs.foldl (fun m x => max m (f x)) 0

/-- One more than the largest argument word the state mentions. -/
def maxArgS (S : SymState) : Nat :=
  max (maxArgList (maxArgList (fun p : String × WExpr => maxArgW p.2)) S.scopes)
    (max (maxArgList (fun p : WExpr × WExpr => max (maxArgW p.1) (maxArgW p.2)) S.writes)
      (max (maxArgList (fun l : Log => max (maxArgList maxArgW l.topics) (maxArgList maxArgO l.data))
        S.logs) (maxArgW S.caller)))

def maxArgF (K : Facts) : Nat := maxArgList (fun p : WExpr × Bool => maxArgW p.1) K

theorem eval_instO (ρ : Val) (base len : Nat) (θ : Nat → WExpr) (o : OByte) :
    (instO base len θ o).eval ρ = o.eval (extV ρ base len fun j => (θ j).eval ρ) := by
  cases o with
  | lit b => rfl
  | byteOf e i => simp only [instO, OByte.eval, eval_instW]

theorem eval_extV_belowO (ρ : Val) (base len : Nat) (f : Nat → Nat) (o : OByte)
    (h : belowO base o = true) : o.eval (extV ρ base len f) = o.eval ρ := by
  cases o with
  | lit b => rfl
  | byteOf e i => simp only [OByte.eval, eval_extV_below ρ base len f e h]

theorem logEval_inst (ρ : Val) (base len : Nat) (θ : Nat → WExpr) (l : Log) :
    Log.eval ρ (instLog base len θ l) = Log.eval (extV ρ base len fun j => (θ j).eval ρ) l := by
  simp only [Log.eval, instLog, List.map_map]
  congr 1
  · apply List.map_congr_left; intro e _; exact eval_instW ρ base len θ e
  · apply List.map_congr_left; intro o _; exact eval_instO ρ base len θ o

theorem logEval_below (ρ : Val) (base len : Nat) (f : Nat → Nat) (l : Log)
    (h : belowLog base l = true) : Log.eval (extV ρ base len f) l = Log.eval ρ l := by
  simp only [belowLog, Bool.and_eq_true, List.all_eq_true] at h
  simp only [Log.eval]
  congr 1
  · apply List.map_congr_left; intro e he; exact eval_extV_below ρ base len f e (h.1 e he)
  · apply List.map_congr_left; intro o ho; exact eval_extV_belowO ρ base len f o (h.2 o ho)

theorem frameOf_instL (ρ : Val) (base len : Nat) (θ : Nat → WExpr) (L : Locals) :
    frameOf ρ (instL base len θ L) = frameOf (extV ρ base len fun j => (θ j).eval ρ) L := by
  simp only [frameOf, instL, List.map_map]
  apply List.map_congr_left
  intro p _
  simp [eval_instW]

theorem frameOfT_instL (ρ : Val) (T : Tags) (base len : Nat) (θ : Nat → WExpr) (L : Locals) :
    frameOfT ρ T (instL base len θ L) = frameOfT (extV ρ base len fun j => (θ j).eval ρ) T L := by
  simp only [frameOfT, instL, List.map_map]
  apply List.map_congr_left
  intro p _
  simp [eval_instW]

theorem frameOf_below (ρ : Val) (base len : Nat) (f : Nat → Nat) (L : Locals)
    (h : (L.all fun p => belowW base p.2) = true) :
    frameOf (extV ρ base len f) L = frameOf ρ L := by
  simp only [List.all_eq_true] at h
  simp only [frameOf]
  apply List.map_congr_left
  intro p hp
  simp [eval_extV_below ρ base len f p.2 (h p hp)]

theorem store_instWs (ρ : Val) (base len : Nat) (θ : Nat → WExpr) (n : Nat) : ∀ ws : Writes,
    Writes.store ρ (instWs base len θ ws) n = Writes.store (extV ρ base len fun j => (θ j).eval ρ) ws n
  | [] => rfl
  | (k, e) :: rest => by
    have ih := store_instWs ρ base len θ n rest
    simp only [instWs, List.map_cons, Writes.store, eval_instW] at ih ⊢
    rw [ih]

theorem store_below (ρ : Val) (base len : Nat) (f : Nat → Nat) (n : Nat) : ∀ ws : Writes,
    belowWs base ws = true → Writes.store (extV ρ base len f) ws n = Writes.store ρ ws n
  | [], _ => rfl
  | (k, e) :: rest, h => by
    simp only [belowWs, List.all_cons, Bool.and_eq_true] at h
    have ih := store_below ρ base len f n rest h.2
    simp only [Writes.store, eval_extV_below ρ base len f k h.1.1, eval_extV_below ρ base len f e h.1.2]
    rw [ih]

theorem hold_extV (ρ : Val) (base len : Nat) (f : Nat → Nat) {K : Facts}
    (hK : factsBelow base K = true) : K.Hold (extV ρ base len f) ↔ K.Hold ρ := by
  simp only [factsBelow, List.all_eq_true] at hK
  constructor
  · intro h p hp
    rw [← eval_extV_below ρ base len f p.1 (hK p hp)]
    exact h p hp
  · intro h p hp
    rw [eval_extV_below ρ base len f p.1 (hK p hp)]
    exact h p hp

theorem lookup_mapSnd {f : List WExpr → List WExpr} : ∀ (l : List (Nat × List WExpr)) (id : Nat),
    (l.map fun p => (p.1, f p.2)).lookup id = (l.lookup id).map f
  | [], _ => rfl
  | (k, ws) :: l, id => by
    by_cases h : id = k
    · subst h; simp [List.lookup]
    · have hb : (id == k) = false := by simp [h]
      simp [List.lookup, hb, lookup_mapSnd l id]

theorem memArr_inst (ρ : Val) (base len : Nat) (θ : Nat → WExpr) (ws : List WExpr) :
    memArr ρ (ws.map (instW base len θ)) = memArr (extV ρ base len fun j => (θ j).eval ρ) ws := by
  simp [memArr, List.map_map, Function.comp_def, eval_instW]

/-- **A runtime the instantiated state shows is one the state shows at the extended valuation.** -/
theorem rel_of_inst {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {base len : Nat}
    {θ : Nat → WExpr} {S : SymState} (hK : factsBelow base E.facts = true)
    (h : StmtRel ρ E ctx rt (instS base len θ S)) :
    StmtRel (extV ρ base len fun j => (θ j).eval ρ) E ctx rt S :=
  StmtRel.congr h h.hash h.ok ((hold_extV ρ base len _ hK).mpr h.facts)
    (by simp only [instS, List.map_map]; apply List.map_congr_left; intro L _
        exact frameOfT_instL ρ S.tags base len θ L)
    (fun k _ => store_instWs ρ base len θ k S.writes)
    (by simp only [instS, List.map_map]; apply List.map_congr_left; intro l _
        exact logEval_inst ρ base len θ l)
    (eval_instW ρ base len θ S.caller)
    (fun id ws' hl => ⟨ws'.map (instW base len θ), by simp [instS, lookup_mapSnd, hl],
      memArr_inst ρ base len θ ws'⟩)
    (fun k hk => by simpa [instS] using hk)

/-- **The converse**: a runtime the state shows at the extended valuation is one the instantiated
state shows. -/
theorem inst_of_rel {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {base len : Nat}
    {θ : Nat → WExpr} {S : SymState} (hK : factsBelow base E.facts = true)
    (h : StmtRel (extV ρ base len fun j => (θ j).eval ρ) E ctx rt S) :
    StmtRel ρ E ctx rt (instS base len θ S) :=
  StmtRel.congr h h.hash h.ok ((hold_extV ρ base len _ hK).mp h.facts)
    (by simp only [instS, List.map_map]; apply List.map_congr_left; intro L _
        exact (frameOfT_instL ρ S.tags base len θ L).symm)
    (fun k _ => (store_instWs ρ base len θ k S.writes).symm)
    (by simp only [instS, List.map_map]; apply List.map_congr_left; intro l _
        exact (logEval_inst ρ base len θ l).symm)
    (eval_instW ρ base len θ S.caller).symm
    (fun id ws' hl => by
      simp only [instS, lookup_mapSnd, Option.map_eq_some_iff] at hl
      obtain ⟨ws, h1, rfl⟩ := hl
      exact ⟨ws, h1, (memArr_inst ρ base len θ ws).symm⟩)
    (fun k hk => by simpa [instS] using hk)

/-! ## The loop's header

The header is the state before the loop with a fresh word for each local, scope by scope in order,
and then for each constant slot in `slots`: the `j`-th fresh word is `.arg (base + j)`, and its
value before the loop is the `j`-th of `entries`. -/

/-- The locals with fresh words from `.arg (base + j)` on. -/
def freshL (base : Nat) : Nat → Locals → Locals
  | _, [] => []
  | j, (x, _) :: rest => (x, .arg (base + j)) :: freshL base (j + 1) rest

/-- The scopes with fresh words from `.arg (base + j)` on. -/
def freshSc (base : Nat) : Nat → Scopes → Scopes
  | _, [] => []
  | j, L :: rest => freshL base j L :: freshSc base (j + L.length) rest

/-- The words of the locals, scope by scope. -/
def wordsSc : Scopes → List WExpr
  | [] => []
  | L :: rest => L.map (·.2) ++ wordsSc rest

/-- The writes with the slots `ks` set to fresh words from `.arg (base + j)` on. -/
def freshWs (base : Nat) : Nat → Writes → List Nat → Writes
  | _, ws, [] => ws
  | j, ws, k :: ks => freshWs base (j + 1) (ws.set (.lit k) (.arg (base + j))) ks

/-- The words a state shows for its locals and for the slots `slots`, in the header's order. -/
def entries (S : SymState) (slots : List Nat) : List WExpr :=
  wordsSc S.scopes ++ slots.map fun k => S.writes.read (.lit k)

/-- **The loop's header**: `S` with fresh words for its locals and the slots `slots`. -/
def header (base : Nat) (S : SymState) (slots : List Nat) : SymState :=
  { S with scopes := freshSc base 0 S.scopes,
           writes := freshWs base (wordsSc S.scopes).length S.writes slots,
           mem := [], next := none }

theorem getD_append_left' {l₁ l₂ : List WExpr} {i : Nat} (d : WExpr) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {l₁ l₂ : List WExpr} (i : Nat) (d : WExpr) :
    (l₁ ++ l₂).getD (l₁.length + i) d = l₂.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem frames_freshL (σ ρ : Val) (base : Nat) : ∀ (L : Locals) (j : Nat),
    (∀ i, i < L.length → (WExpr.arg (base + j + i)).eval σ = ((L.map (fun p : String × WExpr => p.2)).getD i (WExpr.lit 0)).eval ρ) →
    frameOf σ (freshL base j L) = frameOf ρ L
  | [], _, _ => rfl
  | (x, e) :: rest, j, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.map_cons, List.getD_cons_zero] at h0
    have ih := frames_freshL σ ρ base rest (j + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    simp only [freshL, frameOf, List.map_cons] at ih ⊢
    rw [h0, ih]

theorem frames_freshSc (σ ρ : Val) (base : Nat) : ∀ (sc : Scopes) (j : Nat),
    (∀ i, i < (wordsSc sc).length → (WExpr.arg (base + j + i)).eval σ = ((wordsSc sc).getD i (.lit 0)).eval ρ) →
    (freshSc base j sc).map (frameOf σ) = sc.map (frameOf ρ)
  | [], _, _ => rfl
  | L :: rest, j, h => by
    simp only [freshSc, List.map_cons]
    have hL := frames_freshL σ ρ base L j (fun i hi => by
      have := h i (by simp [wordsSc]; omega)
      rw [this]
      simp only [wordsSc]
      rw [getD_append_left' _ (by simpa using hi)])
    have ih := frames_freshSc σ ρ base rest (j + L.length) (fun i hi => by
      have := h (L.length + i) (by simp [wordsSc]; omega)
      have e1 : base + (j + L.length) + i = base + j + (L.length + i) := by omega
      rw [e1, this]
      simp only [wordsSc]
      have := getD_append_right' (l₁ := L.map (·.2)) (l₂ := wordsSc rest) i (.lit 0)
      simp only [List.length_map] at this
      rw [this])
    rw [hL, ih]


theorem framesT_freshL (σ ρ : Val) (T : Tags) (base : Nat) : ∀ (L : Locals) (j : Nat),
    (∀ i, i < L.length → (WExpr.arg (base + j + i)).eval σ = ((L.map (fun p : String × WExpr => p.2)).getD i (WExpr.lit 0)).eval ρ) →
    frameOfT σ T (freshL base j L) = frameOfT ρ T L
  | [], _, _ => rfl
  | (x, e) :: rest, j, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.map_cons, List.getD_cons_zero] at h0
    have ih := framesT_freshL σ ρ T base rest (j + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    simp only [freshL, frameOfT, List.map_cons] at ih ⊢
    rw [h0, ih]

theorem framesT_freshSc (σ ρ : Val) (T : Tags) (base : Nat) : ∀ (sc : Scopes) (j : Nat),
    (∀ i, i < (wordsSc sc).length → (WExpr.arg (base + j + i)).eval σ = ((wordsSc sc).getD i (.lit 0)).eval ρ) →
    (freshSc base j sc).map (frameOfT σ T) = sc.map (frameOfT ρ T)
  | [], _, _ => rfl
  | L :: rest, j, h => by
    simp only [freshSc, List.map_cons]
    have hL := framesT_freshL σ ρ T base L j (fun i hi => by
      have := h i (by simp [wordsSc]; omega)
      rw [this]
      simp only [wordsSc]
      rw [getD_append_left' _ (by simpa using hi)])
    have ih := framesT_freshSc σ ρ T base rest (j + L.length) (fun i hi => by
      have := h (L.length + i) (by simp [wordsSc]; omega)
      have e1 : base + (j + L.length) + i = base + j + (L.length + i) := by omega
      rw [e1, this]
      simp only [wordsSc]
      have := getD_append_right' (l₁ := L.map (·.2)) (l₂ := wordsSc rest) i (.lit 0)
      simp only [List.length_map] at this
      rw [this])
    rw [hL, ih]

theorem store_freshWs (σ ρ : Val) (hρ : ρ.Ok) (base : Nat) (ws0 : Writes) : ∀ (ks : List Nat) (j : Nat) (ws : Writes),
    (∀ n, Writes.store σ ws n = Writes.store ρ ws0 n) →
    (∀ i, i < ks.length → (WExpr.arg (base + j + i)).eval σ = (ws0.read (.lit (ks.getD i 0))).eval ρ) →
    ∀ n, Writes.store σ (freshWs base j ws ks) n = Writes.store ρ ws0 n
  | [], _, _, hws, _, n => hws n
  | k :: ks, j, ws, hws, h, n => by
    simp only [freshWs]
    refine store_freshWs σ ρ hρ base ws0 ks (j + 1) _ ?_ ?_ n
    · intro n
      rw [Writes.store_set]
      have h0 := h 0 (by simp)
      simp only [Nat.add_zero, List.getD_cons_zero] at h0
      rw [h0, Writes.eval_read hρ]
      by_cases hk : (WExpr.lit k).eval σ = n % wordSize
      · rw [ite_eq_left hk]
        simp only [WExpr.eval] at hk ⊢
        rw [hk, Writes.store_mod ρ hρ]
      · rw [ite_eq_right hk, hws n]
    · intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- The valuation of the header before the loop: the fresh words are the words `S` shows at `ρ`. -/
def headVal (ρ : Val) (base : Nat) (S : SymState) (slots : List Nat) : Val :=
  extV ρ base (entries S slots).length fun j => ((entries S slots).getD j (.lit 0)).eval ρ

theorem arg_headVal (ρ : Val) (base : Nat) (S : SymState) (slots : List Nat) (j : Nat)
    (hj : j < (entries S slots).length) :
    (WExpr.arg (base + j)).eval (headVal ρ base S slots) = ((entries S slots).getD j (.lit 0)).eval ρ := by
  simp only [WExpr.eval, headVal, extV_getD]
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left hj,
    Nat.mod_eq_of_lt (WExpr.eval_lt ρ _)]

/-- **Initiation**: a runtime `S` shows at `ρ` is one the header shows at `headVal`. -/
theorem rel_header {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    {base : Nat} (slots : List Nat) (hS : belowS base S = true) (hK : factsBelow base E.facts = true)
    (h : StmtRel ρ E ctx rt S) : StmtRel (headVal ρ base S slots) E ctx rt (header base S slots) := by
  simp only [belowS, Bool.and_eq_true, List.all_eq_true] at hS
  obtain ⟨⟨⟨hsc, hws⟩, hlogs⟩, hcaller⟩ := hS
  have hlen : (entries S slots).length = (wordsSc S.scopes).length + slots.length := by
    simp [entries]
  refine StmtRel.congr h h.hash h.ok ((hold_extV ρ base _ _ hK).mpr h.facts) ?_ ?_ ?_ ?_
    (fun _ _ hl => by simp [header] at hl) (fun _ hk => by simp [header] at hk)
  · simp only [header]
    refine (framesT_freshSc _ ρ S.tags base S.scopes 0 (fun i hi => ?_)).symm
    rw [Nat.add_zero, arg_headVal ρ base S slots i (by omega)]
    simp only [entries]
    rw [getD_append_left' _ hi]
  · intro k _
    simp only [header]
    refine (store_freshWs _ ρ h.ok base S.writes slots _ S.writes
      (fun n => store_below ρ base _ _ n S.writes hws) (fun i hi => ?_) k).symm
    have e1 : base + (wordsSc S.scopes).length + i = base + ((wordsSc S.scopes).length + i) := by omega
    rw [e1]
    refine (arg_headVal ρ base S slots _ (by omega)).trans ?_
    simp only [entries]
    rw [getD_append_right']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem hi]
    rfl
  · simp only [header]
    apply List.map_congr_left
    intro l hl
    exact (logEval_below ρ base _ _ l (hlogs l hl)).symm
  · simp only [header]
    exact (eval_extV_below ρ base _ _ S.caller hcaller).symm

/-! ## The erasure -/

/-- `x++` (or `++x`) of a `uint256`: whether it is postfix, and its target. -/
def incOf? : Stmt → Option (Bool × Expr)
  | .exprStmt (.incDec .add pst (some (.uint 256)) tgt) => some (pst, tgt)
  | _ => none

theorem incOf?_spec {s : Stmt} {pst : Bool} {tgt : Expr} (h : incOf? s = some (pst, tgt)) :
    s = .exprStmt (.incDec .add pst (some (.uint 256)) tgt) := by
  unfold incOf? at h
  split at h <;> cases h
  rfl

/-- **The loop-free erasure with increments**: `eraseStmt`, with blocks erased by itself and the
increments `x++` of a local word (`incVarBr`) and of a word storage field (`incFieldBr`). -/
def eraseInc (E : EraseEnv) : Nat → Stmt → SymState → Option Br
  | 0, _, _ => none
  | n + 1, s, S =>
    match s with
    | .block ss => do
      let b ← eraseSeq (eraseInc E n) ss S.push
      some (b.mapS SymState.pop)
    | s =>
      match incOf? s with
      | some (_, .var x) => do
        let old ← S.word? x
        let L' ← S.setW x (.bin .add old (.lit 1))
        some (incVarBr old L' S)
      | some (_, .storageRead .header x []) => do
        let (k, off, bytes) ← fieldOf? E.fields x
        some (incFieldBr k off bytes S)
      | _ => eraseStmt E (n + 1) s S

/-- A tree of overflow guards before one normal end: the guards and the end's state. -/
def splitG : Br → Option (List WExpr × SymState)
  | .leaf (.normal S) => some ([], S)
  | .ite g (.leaf (.reverted (.panic c))) rest =>
    if c = 0x11 ∧ codeOf g = 0x11 then (splitG rest).map fun p => (g :: p.1, p.2) else none
  | _ => none

theorem splitG_spec : ∀ {b : Br} {gs : List WExpr} {S : SymState}, splitG b = some (gs, S) →
    b = guards gs (.leaf (.normal S))
  | .leaf (.normal S), gs, S', h => by
    simp only [splitG, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .ite g (.leaf (.reverted (.panic c))) rest, gs, S, h => by
    by_cases hc : c = 0x11 ∧ codeOf g = 0x11
    · obtain ⟨rfl, hg⟩ := hc
      simp only [splitG, hg, and_self, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨gs', S'⟩, h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [splitG_spec h']
      simp only [guards, List.foldr_cons, hg]
    · simp only [splitG, hc, ↓reduceIte, reduceCtorEq] at h
  | .leaf (.returned _ _ _), _, _, h | .leaf (.reverted _), _, _, h
  | .ite _ (.leaf (.normal _)) _, _, _, h | .ite _ (.leaf (.returned _ _ _)) _, _, _, h
  | .ite _ (.leaf (.reverted .empty)) _, _, _, h | .ite _ (.leaf (.reverted (.error _))) _, _, _, h
  | .ite _ (.ite _ _ _) _, _, _, h => by simp [splitG] at h

/-- The overflow guard of `w + 1`, as `x++` checks it. -/
def ovf1 (w : WExpr) : WExpr := .bin .lt (.bin .add w (.lit 1)) w

/-- The fresh word whose `+ 1` a guard checks. -/
def guardIdx (base : Nat) : WExpr → Option Nat
  | .bin .lt (.bin .add (.arg a) (.lit 1)) (.arg a') =>
    if a = a' ∧ base ≤ a then some (a - base) else none
  | _ => none

/-- The fresh words whose `+ 1` the guards check, in order. -/
def guardIdxs (base : Nat) : List WExpr → Option (List Nat)
  | [] => some []
  | g :: gs => do
    let j ← guardIdx base g
    let js ← guardIdxs base gs
    some (j :: js)

/-- One iteration at the header `H`: the body and then the update, each a tree of overflow guards
before one normal end. -/
def iterFor (E : EraseEnv) (k : Nat) (post body : Stmt) (H : SymState) :
    Option (List WExpr × SymState) := do
  let bb ← eraseInc E k body H
  let (gb, S1) ← splitG bb
  let pb ← eraseInc E k post S1
  let (gp, S2) ← splitG pb
  some (gb ++ gp, S2)

/-- The constant slots a list of writes names. -/
def litSlots (ws : Writes) : List Nat :=
  ws.filterMap fun p => match p.1 with
    | .lit k => some k
    | _ => none

/-- The fresh word `j` steps when `trs` says so: `.arg (base + j) + 1`, else `.arg (base + j)`. -/
def stepθ (base : Nat) (trs : List Bool) (j : Nat) : WExpr :=
  if trs.getD j false then .bin .add (.arg (base + j)) (.lit 1) else .arg (base + j)

/-- The condition `counter < bound`: the counter's fresh word and the bound, which the iteration
must leave as it is and the counter must step. -/
def condOf (base len : Nat) (trs : List Bool) : List WExpr × WExpr → Option (Nat × WExpr)
  | ([], .bin .lt (.arg a) bnd) =>
    if base ≤ a ∧ a - base < len ∧ trs.getD (a - base) false = true ∧
        instW base len (stepθ base trs) bnd = bnd then some (a - base, bnd) else none
  | _ => none

/-- The words before the loop, in the header's order. -/
def θ0 (S1 : SymState) (slots : List Nat) (j : Nat) : WExpr := (entries S1 slots).getD j (.lit 0)

/-- The number of iterations, over the words before the loop: §bound - counter§ when the counter
is below the bound, else §0§. -/
def itersW (base : Nat) (S1 : SymState) (slots : List Nat) (ji : Nat) (bnd : WExpr) : WExpr :=
  let nb := instW base (entries S1 slots).length (θ0 S1 slots) bnd
  .sel (.bin .lt (θ0 S1 slots ji) nb) (.bin .sub nb (θ0 S1 slots ji)) (.lit 0)

/-- The words after the loop: a stepping word plus the number of iterations, the others as before. -/
def θX (base : Nat) (S1 : SymState) (slots : List Nat) (trs : List Bool) (ji : Nat) (bnd : WExpr)
    (j : Nat) : WExpr :=
  if trs.getD j false then .bin .add (θ0 S1 slots j) (itersW base S1 slots ji bnd) else θ0 S1 slots j

/-- **The closed form of a counted loop**: §Panic(0x11)§ when a checked word plus the number of
iterations wraps, else the header with the words after the loop. -/
def accelBr (base : Nat) (S1 : SymState) (slots : List Nat) (trs : List Bool) (ji : Nat)
    (bnd : WExpr) (js : List Nat) : Br :=
  guards (js.map fun j => .bin .lt (.bin .add (θ0 S1 slots j) (itersW base S1 slots ji bnd)) (θ0 S1 slots j))
    (.leaf (.normal (instS base (entries S1 slots).length (θX base S1 slots trs ji bnd)
      (header base S1 slots))))

/-- The loop's fuel beyond its body's: the iterations are fewer than `2 ^ 256`. -/
def loopFuel : Nat := 2 ^ 256 + 1

/-- **The erasure of a counted loop** from the state `S1` after its `init`, the body and the update
erased with fuel `k`: the closed form, or `none` outside the shape. -/
def accelFor (E : EraseEnv) (k : Nat) (cnd : Expr) (post body : Stmt) (S1 : SymState) : Option Br := do
  let base := max (maxArgS S1) (maxArgF E.facts)
  if belowS base S1 = true ∧ factsBelow base E.facts = true then
    -- the constant slots one iteration writes, from a header with fresh locals
    let (_, S0) ← iterFor E k post body (header base S1 [])
    let slots := litSlots S0.writes
    let H := header base S1 slots
    let ents := entries S1 slots
    let len := ents.length
    let (gs, S2) ← iterFor E k post body H
    let trs := (List.range len).map fun j =>
      (entries S2 slots).getD j (.lit 0) == .bin .add (.arg (base + j)) (.lit 1)
    if S2 = instS base len (stepθ base trs) H then
      let cv ← eraseExpr E.fields H cnd
      let (ji, bnd) ← condOf base len trs cv
      let js ← guardIdxs base gs
      if js.all (fun j => decide (j < len) && trs.getD j false) = true then
        some (accelBr base S1 slots trs ji bnd js)
      else none
    else none
  else none

/-- **The erasure of a statement with counted loops**, with fuel `n`: blocks erased by itself,
`for` loops by `accelFor` (their `init` by `eraseInc`, in the loop's scope, and their body and
update with `loopFuel` less fuel), and every other statement by `eraseInc`. -/
def eraseLoopStmt (E : EraseEnv) : Nat → Stmt → SymState → Option Br
  | 0, _, _ => none
  | n + 1, s, S =>
    match s with
    | .block ss => do
      let b ← eraseSeq (eraseLoopStmt E n) ss S.push
      some (b.mapS SymState.pop)
    | .forLoop init cnd post body =>
      if loopFuel ≤ n then do
        let bi ← eraseInc E n init S.push
        let b ← bi.bind (accelFor E (n - loopFuel) cnd post body)
        some (b.mapS SymState.pop)
      else none
    | s => eraseInc E (n + 1) s S

/-! ## Soundness of the loop-free part -/

/-- A statement list runs as its erasure when each statement does. -/
theorem runs_seq {E : EraseEnv} {n : Nat} {ctx : Context} {f : Stmt → SymState → Option Br}
    (hf : ∀ s S b, f s S = some b → StmtRuns E n ctx s S b) :
    ∀ ss S b, eraseSeq f ss S = some b → ∀ σ rt, StmtRel σ E ctx rt S →
      ∃ r, Stmt.evalList n E.tbl ctx rt ss = .done (.ok r) ∧ LeafRel σ E ctx r (b.eval σ) := by
  intro ss
  induction ss with
  | nil =>
    intro S b h σ rt hrel
    simp only [eraseSeq, Option.some.injEq] at h
    subst h
    exact ⟨.normal rt, by rw [Stmt.evalList]; rfl, hrel⟩
  | cons s rest ihs =>
    intro S b h σ rt hrel
    simp only [eraseSeq, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b1, h1, hb⟩ := h
    obtain ⟨r1, hr1, hl1⟩ := hf s S b1 h1 σ rt hrel
    have hbe := Br.bind_eval σ hb
    simp only [Stmt.evalList, hr1, bind, EvmCompiler.Simulation.Interaction.bind]
    revert hl1 hbe
    cases b1.eval σ with
    | normal S1 =>
      intro hl1 hbe
      obtain ⟨c, hc, hce⟩ := hbe
      cases r1 <;> simp only [LeafRel] at hl1
      rename_i rt1
      obtain ⟨r, hr, hl⟩ := ihs S1 c hc σ rt1 hl1
      exact ⟨r, hr, hce ▸ hl⟩
    | returned S1 vs =>
      intro hl1 hbe
      cases r1 <;> simp only [LeafRel] at hl1
      exact ⟨_, rfl, hbe ▸ hl1⟩
    | reverted p =>
      intro hl1 hbe
      cases p <;> cases r1 <;> simp only [LeafRel] at hl1
      all_goals exact ⟨_, rfl, by rw [hbe]; exact hl1⟩

/-- A block runs as its erasure, in a new scope, popped. -/
theorem runs_block {E : EraseEnv} {n : Nat} {ctx : Context} {f : Stmt → SymState → Option Br}
    (hf : ∀ s S b, f s S = some b → StmtRuns E n ctx s S b) {ss : List Stmt} {S : SymState} {b : Br}
    (h : eraseSeq f ss S.push = some b) :
    StmtRuns E (n + 1) ctx (.block ss) S (b.mapS SymState.pop) := by
  intro σ rt hrel
  obtain ⟨r, hr, hl⟩ := runs_seq hf ss S.push b h σ rt.pushScope hrel.pushScope
  refine ⟨_, eval_block_of hr, ?_⟩
  rw [Br.eval_mapS]
  exact hl.popScope

/-- **A statement runs as its `eraseInc` erasure.** -/
theorem runs_eraseInc (E : EraseEnv) (ctx : Context) :
    ∀ n s S b, eraseInc E n s S = some b → StmtRuns E n ctx s S b
  | 0, _, _, _, h => by simp [eraseInc] at h
  | n + 1, s, S, b, h => by
    unfold eraseInc at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b1, h1, rfl⟩ := h
      exact runs_block (runs_eraseInc E ctx n) h1
    · split at h
      · rename_i pst x hinc
        obtain rfl := incOf?_spec hinc
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨old, hold, L', hL, rfl⟩ := h
        exact stmtRuns_incVar n pst hold hL
      · rename_i pst x hinc
        obtain rfl := incOf?_spec hinc
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨⟨k, off, bytes⟩, hk, rfl⟩ := h
        exact stmtRuns_incField n pst hk
      · exact stmtRuns_of_erase h

/-! ## Soundness of the counted loop -/

theorem iterFor_spec {E : EraseEnv} {k : Nat} {post body : Stmt} {H : SymState} {gs : List WExpr}
    {S2 : SymState} (h : iterFor E k post body H = some (gs, S2)) :
    ∃ gb S1 gp, eraseInc E k body H = some (guards gb (.leaf (.normal S1))) ∧
      eraseInc E k post S1 = some (guards gp (.leaf (.normal S2))) ∧ gs = gb ++ gp := by
  simp only [iterFor, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bb, hbb, ⟨gb, S1⟩, hs1, pb, hpb, ⟨gp, S2'⟩, hs2, he⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [splitG_spec hs1] at hbb
  rw [splitG_spec hs2] at hpb
  exact ⟨gb, S1, gp, hbb, hpb, rfl⟩

theorem guardIdx_spec {base : Nat} {g : WExpr} {j : Nat} (h : guardIdx base g = some j) :
    g = ovf1 (.arg (base + j)) := by
  unfold guardIdx at h
  split at h <;> [split at h; cases h] <;> cases h
  obtain ⟨rfl, hle⟩ := ‹_ ∧ _›
  simp only [ovf1, Nat.add_sub_cancel' hle]

theorem guardIdxs_spec {base : Nat} : ∀ {gs : List WExpr} {js : List Nat},
    guardIdxs base gs = some js → gs = js.map fun j => ovf1 (.arg (base + j))
  | [], js, h => by simp only [guardIdxs, Option.some.injEq] at h; subst h; rfl
  | g :: gs, js, h => by
    simp only [guardIdxs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨j, hj, js', hjs, rfl⟩ := h
    rw [List.map_cons, ← guardIdxs_spec hjs, ← guardIdx_spec hj]

theorem condOf_spec {base len : Nat} {trs : List Bool} {cv : List WExpr × WExpr} {ji : Nat} {bnd : WExpr}
    (h : condOf base len trs cv = some (ji, bnd)) :
    cv = ([], .bin .lt (.arg (base + ji)) bnd) ∧ ji < len ∧ trs.getD ji false = true ∧
      instW base len (stepθ base trs) bnd = bnd := by
  unfold condOf at h
  split at h <;> [split at h; cases h] <;> cases h
  rename_i hc
  exact ⟨by rw [Nat.add_sub_cancel' hc.1], hc.2.1, hc.2.2.1, hc.2.2.2⟩

/-- The words at iteration `t`: a stepping word `t` higher, modulo `2 ^ 256`, the others as before. -/
def valsAt (vs0 : Nat → Nat) (trs : List Bool) (t j : Nat) : Nat :=
  if trs.getD j false then (vs0 j + t) % wordSize else vs0 j

theorem valsAt_lt {vs0 : Nat → Nat} (hv : ∀ j, vs0 j < wordSize) (trs : List Bool) (t j : Nat) :
    valsAt vs0 trs t j < wordSize := by
  unfold valsAt
  split
  · exact Nat.mod_lt _ (by decide)
  · exact hv j

theorem arg_extV (ρ : Val) (base len : Nat) (f : Nat → Nat) {j : Nat} (hj : j < len)
    (hf : f j < wordSize) : (WExpr.arg (base + j)).eval (extV ρ base len f) = f j := by
  simp only [WExpr.eval, extV_getD]
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left hj, Nat.mod_eq_of_lt hf]

theorem one_mod_word : 1 % wordSize = 1 := by decide

theorem step_valsAt (ρ : Val) (base len : Nat) (trs : List Bool) {vs0 : Nat → Nat}
    (hv : ∀ j, vs0 j < wordSize) (t : Nat) :
    extV (extV ρ base len (valsAt vs0 trs t)) base len
        (fun j => (stepθ base trs j).eval (extV ρ base len (valsAt vs0 trs t))) =
      extV ρ base len (valsAt vs0 trs (t + 1)) := by
  rw [extV_extV]
  apply extV_congr
  intro j hj
  have ha := arg_extV ρ base len (valsAt vs0 trs t) hj (valsAt_lt hv trs t j)
  unfold stepθ
  by_cases htr : trs.getD j false = true
  · rw [ite_eq_left htr, eval_bin, ha, eval_lit, one_mod_word]
    simp only [valsAt, htr, ↓reduceIte, BinOp.eval, Nat.mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  · rw [ite_eq_right htr, ha]
    simp only [valsAt, htr]
    rfl

/-- The header's valuation at iteration `t`. -/
def iterV (ρ : Val) (base len : Nat) (vs0 : Nat → Nat) (trs : List Bool) (t : Nat) : Val :=
  extV ρ base len (valsAt vs0 trs t)

theorem guard_ovf1 (σ : Val) (w : WExpr) :
    ((ovf1 w).eval σ != 0) = decide (wordSize ≤ w.eval σ + 1) := by
  have := guard_add σ w (.lit 1)
  rw [eval_lit, one_mod_word] at this
  exact this

theorem leafRel_reverted {σ ρ : Val} {E : EraseEnv} {ctx : Context} {r : Result} {f : Fail}
    (h : LeafRel σ E ctx r (.reverted f)) : LeafRel ρ E ctx r (.reverted f) := by
  cases r <;> simp only [LeafRel] at h ⊢
  exact h

set_option maxHeartbeats 1000000 in
/-- **A counted loop runs as its closed form.** From a runtime whose `init` ends normally in one the
state `S1` shows, the `for` statement ends, at every fuel from `k + loopFuel` on, in a result the
leaf `accelBr` takes there shows: the obligations of `ForObl` hold with the invariant "the header at
iteration `t ≤ N`, no checked word wrapped" and the measure `N - t`. -/
theorem runs_accel {E : EraseEnv} {ctx : Context} {k : Nat} {cnd : Expr} {post body : Stmt}
    {S1 : SymState} {base : Nat} {slots : List Nat} {gs : List WExpr} {S2 : SymState}
    {trs : List Bool} {ji : Nat} {bnd : WExpr} {js : List Nat}
    (hS : belowS base S1 = true) (hK : factsBelow base E.facts = true)
    (hit : iterFor E k post body (header base S1 slots) = some (gs, S2))
    (hS2 : S2 = instS base (entries S1 slots).length (stepθ base trs) (header base S1 slots))
    (hc : eraseExpr E.fields (header base S1 slots) cnd = some ([], .bin .lt (.arg (base + ji)) bnd))
    (hji : ji < (entries S1 slots).length) (htr : trs.getD ji false = true)
    (hbnd : instW base (entries S1 slots).length (stepθ base trs) bnd = bnd)
    (hjs : guardIdxs base gs = some js)
    (hjs' : ∀ j ∈ js, j < (entries S1 slots).length ∧ trs.getD j false = true)
    {init : Stmt} {k0 : Nat} {ρ : Val} {rt rt1 : Runtime}
    (hinit : Stmt.eval k0 E.tbl ctx rt.pushScope init = .done (.ok (.normal rt1)))
    (hrel : StmtRel ρ E ctx rt1 S1) (fuel : Nat) (hf : k + loopFuel ≤ fuel) (hk0 : k0 + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel E.tbl ctx rt (.forLoop init cnd post body) =
        .done (.ok (r.mapRuntime Runtime.popScope)) ∧
      LeafRel ρ E ctx r ((accelBr base S1 slots trs ji bnd js).eval ρ) := by
  obtain ⟨gb, S', gp, hbb, hpb, rfl⟩ := iterFor_spec hit
  have hgs := guardIdxs_spec hjs
  generalize hlen : (entries S1 slots).length = len at *
  generalize hH : header base S1 slots = H at *
  -- the words before the loop, and the header's valuations
  let vs0 : Nat → Nat := fun j => (θ0 S1 slots j).eval ρ
  have hv : ∀ j, vs0 j < wordSize := fun j => WExpr.eval_lt ρ _
  let σ : Nat → Val := iterV ρ base len vs0 trs
  have hσ0 : σ 0 = headVal ρ base S1 slots := by
    simp only [σ, iterV, headVal, hlen]
    apply extV_congr
    intro j _
    simp only [valsAt, vs0, θ0, Nat.add_zero]
    split
    · exact Nat.mod_eq_of_lt (WExpr.eval_lt ρ _)
    · rfl
  have hσ0' : σ 0 = extV ρ base len fun j => (θ0 S1 slots j).eval ρ := by
    rw [hσ0]; simp only [headVal, hlen]; rfl
  have hstep : ∀ t, extV (σ t) base len (fun j => (stepθ base trs j).eval (σ t)) = σ (t + 1) :=
    fun t => step_valsAt ρ base len trs hv t
  have harg : ∀ t j, j < len → (WExpr.arg (base + j)).eval (σ t) = valsAt vs0 trs t j :=
    fun t j hj => arg_extV ρ base len _ hj (valsAt_lt hv trs t j)
  -- the bound does not change
  have hbt : ∀ t, bnd.eval (σ t) = bnd.eval (σ 0) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [← hstep t, ← eval_instW, hbnd, ih]
  -- the counter, the bound and the number of iterations
  let i0 := vs0 ji
  let nb := bnd.eval (σ 0)
  let N := if i0 < nb then nb - i0 else 0
  have hnb : nb < wordSize := WExpr.eval_lt _ _
  have hN : N < wordSize := by simp only [N]; split <;> omega
  have hNw : (itersW base S1 slots ji bnd).eval ρ = N := by
    have e1 : (instW base len (θ0 S1 slots) bnd).eval ρ = nb := by rw [eval_instW, ← hσ0']
    simp only [itersW, hlen, WExpr.eval, e1, BinOp.eval]
    have hi0 : (θ0 S1 slots ji).eval ρ = i0 := rfl
    rw [hi0]
    by_cases h : i0 < nb
    · have e2 : nb + (wordSize - i0) = wordSize + (nb - i0) := by have := hv ji; omega
      simp only [h, ↓reduceIte, N, one_mod_word, e2, Nat.add_mod_left, Nat.one_ne_zero,
        Nat.mod_eq_of_lt (show nb - i0 < wordSize by omega)]
    · simp [h, N]
  have hcnt : ∀ t, t ≤ N → i0 + t < wordSize := by
    intro t ht
    have h1 := hnb
    have h2 := hv ji
    simp only [N] at ht
    split at ht <;> omega
  have hval_i : ∀ t, t ≤ N → valsAt vs0 trs t ji = i0 + t := by
    intro t ht
    simp only [valsAt, htr, ↓reduceIte]
    exact Nat.mod_eq_of_lt (hcnt t ht)
  have hcond : ∀ t, t ≤ N →
      (WExpr.bin .lt (.arg (base + ji)) bnd).eval (σ t) = if i0 + t < nb then 1 else 0 := by
    intro t ht
    rw [eval_bin, harg t ji hji, hval_i t ht, hbt t]
    simp only [BinOp.eval]
    split <;> decide
  have hg : ∀ t j, j ∈ js → vs0 j + t < wordSize →
      ((ovf1 (.arg (base + j))).eval (σ t) != 0) = decide (wordSize ≤ vs0 j + t + 1) := by
    intro t j hj hs
    rw [guard_ovf1, harg t j (hjs' j hj).1]
    simp only [valsAt, (hjs' j hj).2, ↓reduceIte, Nat.mod_eq_of_lt hs]
  have hacc : ∀ j, ((WExpr.bin .lt (.bin .add (θ0 S1 slots j) (itersW base S1 slots ji bnd))
      (θ0 S1 slots j)).eval ρ != 0) = decide (wordSize ≤ vs0 j + N) := by
    intro j
    rw [guard_add, hNw]
  -- the obligations
  let P : Val → Prop := fun σ' => ∃ t, t ≤ N ∧ σ' = σ t ∧ ∀ j ∈ js, vs0 j + t < wordSize
  let m : Val → Nat := fun σ' => N - (σ'.args.getD (base + ji) 0 - i0)
  let Q : Result → Prop := fun r => LeafRel ρ E ctx r ((accelBr base S1 slots trs ji bnd js).eval ρ)
  have hm : ∀ t, t ≤ N → m (σ t) = N - t := by
    intro t ht
    simp only [m, σ, iterV, extV_getD]
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left hji]
    rw [hval_i t ht]
    omega
  -- a guard of the iteration that fires makes the closed form revert
  have hfire : ∀ t, t < N → (∀ j ∈ js, vs0 j + t < wordSize) → ∀ g ∈ gb ++ gp, g.eval (σ t) ≠ 0 →
      (accelBr base S1 slots trs ji bnd js).eval ρ = .reverted (.panic 0x11) := by
    intro t htN hs g hgm hne
    rw [hgs] at hgm
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hgm
    have h1 := hg t j hj (hs j hj)
    have h2 : decide (wordSize ≤ vs0 j + t + 1) = true := by
      rw [← h1]; simpa using hne
    simp only [decide_eq_true_eq] at h2
    unfold accelBr
    rw [guards_eval]
    simp only [failCode_map_lt]
    rw [ite_eq_left]
    rw [List.any_map]
    refine List.any_eq_true.mpr ⟨j, hj, ?_⟩
    simp only [Function.comp, hacc j, decide_eq_true_eq]
    omega
  have hobl : ForObl k E ctx cnd post body H P m Q (.bin .lt (.arg (base + ji)) bnd)
      (guards gb (.leaf (.normal S'))) := by
    refine ⟨hc, runs_eraseInc E ctx k body H _ hbb, ?_, ?_⟩
    · -- exit: the condition is false only at iteration N, where nothing wrapped
      rintro σ' rt' ⟨t, ht, rfl, hs⟩ hrel' hz
      have htN : t = N := by
        rw [hcond t ht] at hz
        simp only [N] at ht ⊢
        split at hz
        · cases hz
        · split at ht <;> split <;> omega
      subst htN
      show LeafRel ρ E ctx (.normal rt') ((accelBr base S1 slots trs ji bnd js).eval ρ)
      unfold accelBr
      rw [guards_eval, ite_eq_right]
      · simp only [Br.eval, LeafRel]
        rw [hlen, hH]
        apply inst_of_rel hK
        have : (extV ρ base len fun j => (θX base S1 slots trs ji bnd j).eval ρ) = σ N := by
          apply extV_congr
          intro j _
          simp only [θX, valsAt]
          split
          · rw [eval_bin, hNw]; simp only [BinOp.eval, Nat.mod_mod]; rfl
          · rfl
        rw [this]
        exact hrel'
      · rw [List.any_map]
        simp only [List.any_eq_true, not_exists, not_and, Function.comp, hacc, decide_eq_true_eq]
        intro j hj
        have := hs j hj
        omega
    · -- iteration
      rintro σ' ⟨t, ht, rfl, hs⟩ hnz
      have htN : t < N := by
        rw [hcond t ht] at hnz
        simp only [N] at ht ⊢
        split at hnz
        · split <;> omega
        · exact absurd rfl hnz
      rw [guards_eval]
      by_cases hgb : gb.any (fun g => g.eval (σ t) != 0) = true
      · rw [ite_eq_left hgb]
        intro r hr
        obtain ⟨g, hgm, hne⟩ := List.any_eq_true.mp hgb
        show LeafRel ρ E ctx r _
        rw [hfire t htN hs g (List.mem_append_left _ hgm) (by simpa using hne)]
        have hc : failCode (σ t) gb = 0x11 := failCode_of_codes _ (fun g' hg' => by
          have hm := List.mem_append_left gp hg'
          rw [hgs] at hm
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hm
          rfl)
        rw [hc] at hr
        exact leafRel_reverted hr
      rw [ite_eq_right hgb]
      refine ⟨guards gp (.leaf (.normal S2)), runs_eraseInc E ctx k post S' _ hpb, ?_⟩
      rw [guards_eval]
      by_cases hgp : gp.any (fun g => g.eval (σ t) != 0) = true
      · rw [ite_eq_left hgp]
        intro r hr
        obtain ⟨g, hgm, hne⟩ := List.any_eq_true.mp hgp
        show LeafRel ρ E ctx r _
        rw [hfire t htN hs g (List.mem_append_right _ hgm) (by simpa using hne)]
        have hc : failCode (σ t) gp = 0x11 := failCode_of_codes _ (fun g' hg' => by
          have hm := List.mem_append_right gb hg'
          rw [hgs] at hm
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hm
          rfl)
        rw [hc] at hr
        exact leafRel_reverted hr
      rw [ite_eq_right hgp]
      refine ⟨σ (t + 1), ⟨t + 1, by omega, rfl, ?_⟩, ?_, ?_⟩
      · intro j hj
        have hmem : ovf1 (.arg (base + j)) ∈ gb ++ gp := by
          rw [hgs]; exact List.mem_map.mpr ⟨j, hj, rfl⟩
        have hz : (ovf1 (.arg (base + j))).eval (σ t) = 0 := by
          rcases List.mem_append.mp hmem with h | h
          · by_contra hne
            exact hgb (List.any_eq_true.mpr ⟨_, h, by simpa using hne⟩)
          · by_contra hne
            exact hgp (List.any_eq_true.mpr ⟨_, h, by simpa using hne⟩)
        have h1 := hg t j hj (hs j hj)
        rw [hz] at h1
        simp only [bne_self_eq_false, Bool.false_eq, decide_eq_false_iff_not] at h1
        omega
      · rw [hm (t + 1) (by omega), hm t ht]
        omega
      · intro rt' hrel'
        rw [hS2] at hrel'
        rw [← hstep t]
        exact rel_of_inst hK hrel'
  have hp0 : P (σ 0) := ⟨0, Nat.zero_le _, rfl, fun j _ => by simpa using hv j⟩
  have hrel0 : StmtRel (σ 0) E ctx rt1 H := by
    rw [hσ0, ← hH]
    exact rel_header slots hS hK hrel
  refine forLoop_of_erased hobl hinit hp0 hrel0 fuel ?_ hk0
  rw [hm 0 (Nat.zero_le _)]
  have hlf : loopFuel = wordSize + 1 := rfl
  omega

theorem accelFor_spec {E : EraseEnv} {k : Nat} {cnd : Expr} {post body : Stmt} {S1 : SymState}
    {b : Br} (h : accelFor E k cnd post body S1 = some b) :
    ∃ base slots gs S2 trs ji bnd js, belowS base S1 = true ∧ factsBelow base E.facts = true ∧
      iterFor E k post body (header base S1 slots) = some (gs, S2) ∧
      S2 = instS base (entries S1 slots).length (stepθ base trs) (header base S1 slots) ∧
      eraseExpr E.fields (header base S1 slots) cnd = some ([], .bin .lt (.arg (base + ji)) bnd) ∧
      ji < (entries S1 slots).length ∧ trs.getD ji false = true ∧
      instW base (entries S1 slots).length (stepθ base trs) bnd = bnd ∧
      guardIdxs base gs = some js ∧
      (∀ j ∈ js, j < (entries S1 slots).length ∧ trs.getD j false = true) ∧
      b = accelBr base S1 slots trs ji bnd js := by
  unfold accelFor at h
  dsimp only at h
  split at h
  · rename_i hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨g0, S0⟩, _, h⟩ := h
    dsimp only at h
    obtain ⟨⟨gs, S2⟩, hit, h⟩ := h
    dsimp only at h
    split at h
    · rename_i hS2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨cv, hcv, h⟩ := h
      obtain ⟨⟨ji, bnd⟩, hco, h⟩ := h
      dsimp only at h
      obtain ⟨js, hjs, h⟩ := h
      split at h
      · rename_i hall
        try simp only [Option.some.injEq] at h
        obtain ⟨rfl, hji, htr, hbnd⟩ := condOf_spec hco
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
        exact ⟨_, _, gs, S2, _, ji, bnd, js, hb.1, hb.2, hit, hS2, hcv, hji, htr, hbnd, hjs, hall, h.symm⟩
      · cases h
    · cases h
  · cases h

/-- A `for` statement whose `init` does not end normally ends as it, its scope closed. -/
theorem forLoop_stop {n : Nat} {tbl : FunctionTable} {ctx : Context} {rt : Runtime} {init : Stmt}
    {cnd : Expr} {post body : Stmt} {r : Result}
    (h : Stmt.eval n tbl ctx rt.pushScope init = .done (.ok r)) (hr : ∀ rt', r ≠ .normal rt') :
    Stmt.eval (n + 1) tbl ctx rt (.forLoop init cnd post body) =
      .done (.ok (r.mapRuntime Runtime.popScope)) := by
  simp only [Stmt.eval]
  rw [h, bind_done_ok]
  cases r with
  | normal rt' => exact absurd rfl (hr rt')
  | _ => rfl

/-- **A statement runs as its `eraseLoopStmt` erasure.** -/
theorem runs_eraseLoop (E : EraseEnv) (ctx : Context) :
    ∀ n s S b, eraseLoopStmt E n s S = some b → StmtRuns E n ctx s S b
  | 0, _, _, _, h => by simp [eraseLoopStmt] at h
  | n + 1, s, S, b, h => by
    unfold eraseLoopStmt at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b1, h1, rfl⟩ := h
      exact runs_block (runs_eraseLoop E ctx n) h1
    · rename_i init cnd post body
      split at h
      · rename_i hfuel
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨bi, hbi, b', hb', rfl⟩ := h
        intro σ rt hrel
        obtain ⟨r0, hr0, hl0⟩ := runs_eraseInc E ctx n init S.push bi hbi σ rt.pushScope hrel.pushScope
        have hbe := Br.bind_eval σ hb'
        rw [Br.eval_mapS]
        revert hl0 hbe
        cases bi.eval σ with
        | normal S1 =>
          intro hl0 hbe
          obtain ⟨c, hc, hce⟩ := hbe
          cases r0 <;> simp only [LeafRel] at hl0
          rename_i rt1
          obtain ⟨base, slots, gs, S2, trs, ji, bnd, js, hS, hK, hit, hS2, hcv, hji, htr, hbnd, hjs,
            hall, rfl⟩ := accelFor_spec hc
          have hlf : loopFuel = wordSize + 1 := rfl
          obtain ⟨r, hr, hl⟩ := runs_accel hS hK hit hS2 hcv hji htr hbnd hjs hall hr0 hl0 (n + 1)
            (by omega) (by omega)
          exact ⟨_, hr, by rw [hce]; exact hl.popScope⟩
        | returned S1 vs =>
          intro hl0 hbe
          cases r0 <;> simp only [LeafRel] at hl0
          exact ⟨_, forLoop_stop hr0 (fun _ h => by cases h), by rw [hbe]; exact LeafRel.popScope hl0⟩
        | reverted p =>
          intro hl0 hbe
          cases r0 <;> simp only [LeafRel] at hl0
          exact ⟨_, forLoop_stop hr0 (fun _ h => by cases h), by
            rw [hbe]; exact LeafRel.popScope (l := .reverted p) (by simpa only [LeafRel] using hl0)⟩
      · cases h
    · exact runs_eraseInc E ctx (n + 1) s S b h

/-- **A body with counted loops runs as its erasure**: `BodyRuns` from `eraseLoopStmt`. -/
theorem bodyRuns_of_eraseLoop {E : EraseEnv} {fuel : Nat} {fn : FunctionDef} {b : Br}
    (h : eraseLoopStmt E fuel fn.body (initState fn) = some b) : BodyRuns E fuel fn b :=
  fun ρ ctx rt hrel => runs_eraseLoop E ctx fuel fn.body (initState fn) b h ρ rt hrel

/-- info: 'SolidCore.Refinement.Generic.Loop.runs_accel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runs_accel

/-- info: 'SolidCore.Refinement.Generic.Loop.runs_eraseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runs_eraseLoop

/-- info: 'SolidCore.Refinement.Generic.Loop.bodyRuns_of_eraseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bodyRuns_of_eraseLoop
end SolidCore.Refinement.Generic.Loop

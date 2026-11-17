import Verify.LoopSource.Equiv.Run
import Verify.VC.Discharge

/-!
# The leaves' obligations, decided

`checkWith` decides `Obl` for the leaves of a cut-point check from an invariant `I` (formulas
over a header valuation's words) and a measure `μ` (a word), with no per-contract proof: every
obligation is a list of formulas refuted by solar-verify's verified decision procedure `refuteOb`
(`Verify/VC/Discharge.lean`). A word becomes an integer term in which every operation is an
uninterpreted function (`tr`), which `env ρ` interprets exactly as `WExpr.eval ρ`; for the
operations a loop's arithmetic uses (addition, subtraction, comparison), `defs` states their meaning
as case splits the procedure decides. `infer` finds `I` and `μ` from the leaves; it is untrusted, as
only `checkWith` is proved sound (`Obl.lean`).
-/

namespace Verify.LoopSource.Equiv.Inv
open SolarTV SolidCore.Refinement.Generic Verify.LoopSource.Equiv
open SolidCore.Verify.VC (Tm refuteOb)

/-! ## Words as integer terms -/

/-- `2 ^ 256`. -/
def W : Nat := wordSize

def binCode : BinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .lt => 4 | .gt => 5 | .eq => 6 | .and => 7
  | .or => 8 | .xor => 9 | .shl => 10 | .shr => 11 | .byte => 12

def binOf : Nat → BinOp
  | 0 => .add | 1 => .sub | 2 => .mul | 3 => .div | 4 => .lt | 5 => .gt | 6 => .eq | 7 => .and
  | 8 => .or | 9 => .xor | 10 => .shl | 11 => .shr | _ => .byte

theorem binOf_code (op : BinOp) : binOf (binCode op) = op := by cases op <;> rfl

def unCode : UnOp → Nat
  | .iszero => 0 | .not => 1

def unOf : Nat → UnOp
  | 0 => .iszero | _ => .not

theorem unOf_code (op : UnOp) : unOf (unCode op) = op := by cases op <;> rfl

/-- A word as an integer term: a literal is its numeral, every other word an uninterpreted
function of its parts. -/
def tr : WExpr → Tm
  | .lit v => .num (v % W)
  | .arg i => .app "w.arg" [.num i]
  | .init k => .app "w.init" [.num k]
  | .un op a => .app "w.un" [.num (unCode op), tr a]
  | .bin op a b => .app "w.bin" [.num (binCode op), tr a, tr b]
  | .sinit k => .app "w.sinit" [tr k]
  | .sel c a b => .app "w.sel" [tr c, tr a, tr b]
  | .hash a b => .app "w.hash" [tr a, tr b]
  | .caller => .app "w.caller" [.num 0]

/-- The uninterpreted functions of `tr`, as `WExpr.eval ρ` computes them. -/
def uOf (ρ : Val) (f : String) (xs : List Int) : Int :=
  match f, xs with
  | "w.arg", [i] => ((ρ.args.getD i.toNat 0 % W : Nat) : Int)
  | "w.init", [k] => ((ρ.store k.toNat % W : Nat) : Int)
  | "w.un", [c, a] => (((unOf c.toNat).eval a.toNat % W : Nat) : Int)
  | "w.bin", [c, a, b] => (((binOf c.toNat).eval a.toNat b.toNat % W : Nat) : Int)
  | "w.sinit", [k] => ((ρ.store k.toNat % W : Nat) : Int)
  | "w.sel", [c, a, b] => if c = 0 then b else a
  | "w.hash", [a, b] => ((ρ.hash a.toNat b.toNat % W : Nat) : Int)
  | "w.caller", [_] => ((ρ.caller % W : Nat) : Int)
  | _, _ => 0

/-- The environment of a valuation. -/
def env (ρ : Val) : SolidCore.Verify.VC.Env :=
  { i := fun _ => 0, b := fun _ => False, a := fun _ _ => 0, u := uOf ρ }

/-! ## Formulas over words -/

/-- A formula over a valuation's words. -/
inductive F where
  | fact (e : WExpr) (b : Bool)
  | le (a b : WExpr)
  | lt (a b : WExpr)
  | eq (a b : WExpr)
  /-- `a + d = b + c` as integers. -/
  | lin (a b c d : WExpr)
  | or (f g : F)
  | not (f : F)
  deriving DecidableEq, Repr

/-- What a formula says of a valuation. -/
def F.Holds (ρ : Val) : F → Prop
  | .fact e b => (e.eval ρ = 0 ↔ b = false)
  | .le a b => a.eval ρ ≤ b.eval ρ
  | .lt a b => a.eval ρ < b.eval ρ
  | .eq a b => a.eval ρ = b.eval ρ
  | .lin a b c d => a.eval ρ + d.eval ρ = b.eval ρ + c.eval ρ
  | .or f g => f.Holds ρ ∨ g.Holds ρ
  | .not f => ¬ f.Holds ρ

def F.tr : F → Tm
  | .fact e b => if b then .app "not" [.app "=" [Inv.tr e, .num 0]] else .app "=" [Inv.tr e, .num 0]
  | .le a b => .app "<=" [Inv.tr a, Inv.tr b]
  | .lt a b => .app "<" [Inv.tr a, Inv.tr b]
  | .eq a b => .app "=" [Inv.tr a, Inv.tr b]
  | .lin a b c d => .app "=" [.app "+" [Inv.tr a, Inv.tr d], .app "+" [Inv.tr b, Inv.tr c]]
  | .or f g => .app "or" [f.tr, g.tr]
  | .not f => .app "not" [f.tr]

/-- The words a formula compares. -/
def F.words : F → List WExpr
  | .fact e _ => [e]
  | .le a b | .lt a b | .eq a b => [a, b]
  | .lin a b c d => [a, b, c, d]
  | .or f g => f.words ++ g.words
  | .not f => f.words

/-- A word and its parts. -/
def subs : WExpr → List WExpr
  | .lit v => [.lit v]
  | .arg i => [.arg i]
  | .init k => [.init k]
  | .un op a => .un op a :: subs a
  | .bin op a b => .bin op a b :: (subs a ++ subs b)
  | .sinit k => .sinit k :: subs k
  | .sel c a b => .sel c a b :: (subs c ++ subs a ++ subs b)
  | .hash a b => .hash a b :: (subs a ++ subs b)
  | .caller => [.caller]

/-- Every word is a word. -/
def rng (e : WExpr) : List Tm := [.app "<=" [.num 0, tr e], .app "<=" [tr e, .num (W - 1)]]

/-- For the arithmetic of loops, a word's value by cases. -/
def defs (e : WExpr) : List Tm :=
  let t := tr e
  match e with
    | .bin .add a b =>
      let s := Tm.app "+" [tr a, tr b]
      [.app "or" [.app "and" [.app "<" [s, .num W], .app "=" [t, s]],
        .app "and" [.app "<=" [.num W, s], .app "=" [t, .app "-" [s, .num W]]]]]
    | .bin .sub a b =>
      let d := Tm.app "-" [tr a, tr b]
      [.app "or" [.app "and" [.app "<=" [tr b, tr a], .app "=" [t, d]],
        .app "and" [.app "<" [tr a, tr b], .app "=" [t, .app "+" [d, .num W]]]]]
    | .bin .lt a b =>
      [.app "or" [.app "and" [.app "<" [tr a, tr b], .app "=" [t, .num 1]],
        .app "and" [.app "<=" [tr b, tr a], .app "=" [t, .num 0]]]]
    | .bin .gt a b =>
      [.app "or" [.app "and" [.app "<" [tr b, tr a], .app "=" [t, .num 1]],
        .app "and" [.app "<=" [tr a, tr b], .app "=" [t, .num 0]]]]
    | .bin .eq a b =>
      [.app "or" [.app "and" [.app "=" [tr a, tr b], .app "=" [t, .num 1]],
        .app "and" [.app "not" [.app "=" [tr a, tr b]], .app "=" [t, .num 0]]]]
    | .un .iszero a =>
      [.app "or" [.app "and" [.app "=" [tr a, .num 0], .app "=" [t, .num 1]],
        .app "and" [.app "not" [.app "=" [tr a, .num 0]], .app "=" [t, .num 0]]]]
    | _ => []

/-- **The terms of an obligation**: the facts of every word the formulas read, and the formulas. -/
def obIn (keep : WExpr → Bool) (hyps : List F) : List Tm :=
  let ws := ((hyps.flatMap F.words).flatMap subs).eraseDups
  ws.flatMap rng ++ hyps.map F.tr ++ (ws.filter keep).flatMap defs

def ob (hyps : List F) : List Tm := obIn (fun _ => true) hyps

/-- **The formulas have no common valuation.** -/
def refutes (n : Nat) (hyps : List F) : Bool :=
  refuteOb (obIn (fun e => !argsBelow n e) hyps) || refuteOb (ob hyps)

/-- The argument and storage words a word reads. -/
def leaves : WExpr → List WExpr
  | .lit _ => []
  | .arg i => [.arg i]
  | .init k => [.init k]
  | .un _ a => leaves a
  | .bin _ a b => leaves a ++ leaves b
  | .sinit k => .sinit k :: leaves k
  | .sel c a b => leaves c ++ leaves a ++ leaves b
  | .hash a b => .hash a b :: (leaves a ++ leaves b)
  | .caller => [.caller]

def F.leaves (f : F) : List WExpr := f.words.flatMap Inv.leaves

/-- One round of the slice: the hypotheses that read a word of `ls`, and the words they read. -/
def sliceStep (hyps : List F) (ls : List WExpr) : List WExpr :=
  (ls ++ (hyps.filter fun h => h.leaves.any (· ∈ ls)).flatMap F.leaves).eraseDups

def sliceLeaves (hyps : List F) : Nat → List WExpr → List WExpr
  | 0, ls => ls
  | k + 1, ls =>
    let ls' := sliceStep hyps ls
    if ls'.length = ls.length then ls else sliceLeaves hyps k ls'

/-- **The hypotheses within `k` rounds of the goal's words**: those that read only words reached
from the goal's in `k` rounds. -/
def slice (k : Nat) (hyps : List F) (seed : List F) : List F :=
  let ls := sliceLeaves hyps k (seed.flatMap F.leaves).eraseDups
  hyps.filter fun h => h.leaves.all (· ∈ ls)

/-- `hyps ⊢ goal`, from the hypotheses it depends on. -/
def proves (n : Nat) (S K : List F) (goal : F) : Bool :=
  S.contains goal || K.contains goal || refutes n (slice 0 S (goal :: K) ++ K ++ [.not goal]) ||
    refutes n (slice 1 S (goal :: K) ++ K ++ [.not goal])

/-! ## Header valuations -/

/-- The word with argument `n + k` replaced by the `k`-th header word, as `nextVal` reads it. -/
def sub (n : Nat) (hs : List WExpr) : WExpr → WExpr
  | .lit v => .lit v
  | .arg i => if i < n then .arg i else (hs[i - n]?).getD (.lit 0)
  | .init k => .init k
  | .un op a => .un op (sub n hs a)
  | .bin op a b => .bin op (sub n hs a) (sub n hs b)
  | .sinit k => .sinit (sub n hs k)
  | .sel c a b => .sel (sub n hs c) (sub n hs a) (sub n hs b)
  | .hash a b => .hash (sub n hs a) (sub n hs b)
  | .caller => .caller

def F.sub (n : Nat) (hs : List WExpr) : F → F
  | .fact e b => .fact (Inv.sub n hs e) b
  | .le a b => .le (Inv.sub n hs a) (Inv.sub n hs b)
  | .lt a b => .lt (Inv.sub n hs a) (Inv.sub n hs b)
  | .eq a b => .eq (Inv.sub n hs a) (Inv.sub n hs b)
  | .lin a b c d => .lin (Inv.sub n hs a) (Inv.sub n hs b) (Inv.sub n hs c) (Inv.sub n hs d)
  | .or f g => .or (f.sub n hs) (g.sub n hs)
  | .not f => .not (f.sub n hs)

/-- A path's facts as formulas. -/
def factsF (K : Facts) : List F := K.map fun p => .fact p.1 p.2

/-- No case holds. -/
def noCase (c : Facts) : F := c.foldr (fun p g => .or (.not (.fact p.1 p.2)) g) (.lt (.lit 0) (.lit 0))

/-! ## Trees -/

/-- The leaves of a tree, each with the sides of the words it branches on. -/
def paths : Tree → List (Facts × Tree)
  | .halt ok out ws ls => [([], .halt ok out ws ls)]
  | .ite c t e => (paths t).map (fun p => ((c, true) :: p.1, p.2)) ++
      (paths e).map (fun p => ((c, false) :: p.1, p.2))

/-- The word a slot holds after writes to literal slots. `none` when a write's slot is not a
literal. -/
def readLit (K : Nat) : Writes → Option WExpr
  | [] => some (.init K)
  | (.lit k, e) :: ws => if k % W = K then some e else readLit K ws
  | _ :: _ => none

/-- The literal slots of writes, mod `2 ^ 256`. -/
def keysLit : Writes → List Nat
  | [] => []
  | (.lit k, _) :: ws => (k % W) :: keysLit ws
  | _ :: ws => keysLit ws

def isLitKey (w : WExpr × WExpr) : Bool :=
  match w.1 with
  | .lit _ => true
  | _ => false

def isLitByte : OByte → Bool
  | .lit _ => true
  | _ => false

/-- **What two ends must agree on**, as goals: their outputs (constant bytes, compared after normal
forms), their logs (none) and, on success, the words every written slot holds; ends of different
success must be unreachable. `none` outside this procedure. -/
def haltGoals : Tree → Tree → Option (List F)
  | .halt ok out ws ls, .halt ok' out' ws' ls' =>
    if ok ≠ ok' then some [.lt (.lit 0) (.lit 0)]
    else if out.map OByte.norm = out'.map OByte.norm ∧ (out.map OByte.norm).all isLitByte = true ∧
        ls = [] ∧ ls' = [] ∧ ws.all isLitKey = true ∧ ws'.all isLitKey = true then
      if ok then
        (keysLit ws ++ keysLit ws').mapM fun K => do
          let a ← readLit K ws
          let b ← readLit K ws'
          some (.eq a b)
      else some []
    else none
  | _, _ => none

/-- \`S, K\` have no common valuation: from all of \`K\` and the formulas of \`S\` that read \`K\`'s words,
then those one round further. -/
def refutesSl (n : Nat) (S K : List F) : Bool :=
  refutes n (slice 0 S K ++ K) || refutes n (slice 1 S K ++ K)

/-- **An end agrees with a tree** under the invariant \`S\` and the path's facts \`K\`: for every
path of each, the path is unreachable or the two ends agree. -/
def exitOk (n : Nat) (S K : List F) (T' T : Tree) : Bool :=
  (paths T').all fun p' => (paths T).all fun p =>
    let k := K ++ factsF p'.1 ++ factsF p.1
    refutesSl n S k || match haltGoals p'.2 p.2 with
      | some gs => gs.all (proves n S k)
      | none => false

/-- No argument word at or past `n` in a tree. -/
def treeBelow (n : Nat) : Tree → Bool
  | .halt _ out ws ls =>
    out.all (fun b => match b with | .lit _ => true | .byteOf e _ => argsBelow n e) &&
    ws.all (fun w => argsBelow n w.1 && argsBelow n w.2) &&
    ls.all (fun l => l.topics.all (argsBelow n) &&
      l.data.all (fun b => match b with | .lit _ => true | .byteOf e _ => argsBelow n e))
  | .ite c t e => argsBelow n c && treeBelow n t && treeBelow n e

/-! ## The check -/

/-- `f` holds at every arrival: from the entry under the path's facts, from the header under the
invariant `S` and the path's facts. -/
def holdsAfter (n : Nat) (le li : List (Facts × Out)) (S : List F) (f : F) : Bool :=
  (le.all fun p => match p.2 with
    | .back hs => proves n [] (factsF p.1) (f.sub n hs)
    | .exit _ => true) &&
  (li.all fun p => match p.2 with
    | .back hs => proves n S (factsF p.1) (f.sub n hs)
    | .exit _ => true)

/-- One obligation of the check. -/
inductive Task where
  /-- The source's tree reads only the call's words. -/
  | below
  /-- Invariant formula `f` holds after the arrival `p`, of the entry run or of an iteration run. -/
  | inv (f : F) (entry : Bool) (p : Facts × Out)
  /-- An end of the entry run is the source's tree. -/
  | entryEnd (p : Facts × Out)
  /-- An end of an iteration run is the source's tree; a back edge lowers the measure. -/
  | iterLeaf (p : Facts × Out)
  /-- Some case holds wherever the invariant does. -/
  | cover
  deriving Repr

/-- Whether an obligation holds, for invariant `I` and measure `μ`. -/
def Task.ok (n : Nat) (cases : List Facts) (T : Tree) (I : List F) (μ : WExpr) : Task → Bool
  | .below => treeBelow n T
  | .inv f entry p => match p.2 with
    | .back hs => proves n (if entry then [] else I) (factsF p.1) (f.sub n hs)
    | .exit _ => true
  | .entryEnd p => match p.2 with
    | .exit T' => exitOk n [] (factsF p.1) T' T
    | .back _ => true
  | .iterLeaf p => match p.2 with
    | .exit T' => exitOk n I (factsF p.1) T' T
    | .back hs => proves n I (factsF p.1) (.lt (Inv.sub n hs μ) μ)
  | .cover => proves n I (cases.map noCase) (.lt (.lit 0) (.lit 0))

/-- The obligations of the leaves `le` (entry run) and `li` (iteration runs) for invariant `I`. -/
def tasks (le li : List (Facts × Out)) (I : List F) : List Task :=
  [.below] ++ I.flatMap (fun f => le.map (.inv f true) ++ li.map (.inv f false)) ++
    le.map .entryEnd ++ li.map .iterLeaf ++ [.cover]

/-- **The check of the obligations** for invariant `I` and measure `μ`: every task holds. -/
def checkWith (n : Nat) (cases : List Facts) (T : Tree) (le li : List (Facts × Out)) (I : List F)
    (μ : WExpr) : Bool :=
  (tasks le li I).all (Task.ok n cases T I μ)

/-- The check from each task by its index, for one kernel check per task. -/
theorem checkWith_of_each {n : Nat} {cases : List Facts} {T : Tree} {le li : List (Facts × Out)}
    {I : List F} {μ : WExpr}
    (h : ∀ i (hi : i < (tasks le li I).length), ((tasks le li I)[i]).ok n cases T I μ = true) :
    checkWith n cases T le li I μ = true := by
  unfold checkWith
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  exact h i hi

/-- A check fails when one of its tasks does. -/
theorem checkWith_false {n : Nat} {cases : List Facts} {T : Tree} {le li : List (Facts × Out)}
    {I : List F} {μ : WExpr} {t : Task} (hm : t ∈ tasks le li I) (h : t.ok n cases T I μ = false) :
    checkWith n cases T le li I μ = false := by
  unfold checkWith
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  rw [hall t hm] at h
  exact Bool.noConfusion h

/-! ## Inference (untrusted) -/

def hw (n k : Nat) : WExpr := .arg (n + k)

def entryOf (le : List (Facts × Out)) : Option (Facts × List WExpr) :=
  match le.filterMap (fun p => match p.2 with | .back hs => some (p.1, hs) | _ => none) with
  | [e] => some e
  | _ => none

def backs (li : List (Facts × Out)) : List (Facts × List WExpr) :=
  li.filterMap fun p => match p.2 with | .back hs => some (p.1, hs) | _ => none

def steps (n : Nat) (li : List (Facts × Out)) (k c : Nat) : Bool :=
  (backs li).all fun b => b.2[k]? == some (.bin .add (hw n k) (.lit c))

def setsTo (li : List (Facts × Out)) (k c : Nat) : Bool :=
  (backs li).all fun b => b.2[k]? == some (.lit c)

def exitTests (n : Nat) (li : List (Facts × Out)) : List (Nat × WExpr) :=
  (li.flatMap (·.1)).filterMap fun p => match p.1 with
    | .bin .lt (.arg i) b => if n ≤ i ∧ argsBelow n b then some (i - n, b) else none
    | _ => none

/-- The exit tests `h ≠ 0` of the iteration runs' facts. -/
def nzTests (n : Nat) (li : List (Facts × Out)) : List Nat :=
  ((li.flatMap (·.1)).filterMap fun p => match p.1 with
    | .un .iszero (.bin .eq (.arg i) (.lit 0)) => if n ≤ i then some (i - n) else none
    | _ => none).eraseDups

/-- Candidates: the call's facts at the entry arrival, header words no back edge changes, pairs of
words stepping together, exit-test bounds and two-valued flags. -/
def cands (n nhw : Nat) (le li : List (Facts × Out)) : List F :=
  match entryOf le with
  | none => []
  | some (K, E) =>
    let ks := List.range nhw
    let call := K.filterMap fun p => if argsBelow n p.1 then some (F.fact p.1 p.2) else none
    let same := ks.filterMap fun k =>
      if (backs li).all (fun b => b.2[k]? == some (hw n k)) then (E[k]?).map (F.eq (hw n k)) else none
    let step := ks.filter (fun k => steps n li k 1)
    let rel := step.flatMap fun k => step.filterMap fun j =>
      if j ≤ k then none else
      match E[k]?, E[j]? with
      | some ek, some ej => some (F.lin (hw n k) ek (hw n j) ej)
      | _, _ => none
    -- A word that counts up to 0 in steps of one counts what is left: `h_j + (0 - h_k)` stays.
    let left := (nzTests n li).filter (· ∈ step) |>.flatMap fun k => step.filterMap fun j =>
      if j = k then none else
      match E[k]?, E[j]? with
      | some ek, some ej => some (F.lin (hw n j) ej (.bin .sub (.lit 0) ek) (.bin .sub (.lit 0) (hw n k)))
      | _, _ => none
    let bnd := (exitTests n li).filterMap fun t => if t.1 ∈ step then some (F.le (hw n t.1) t.2) else none
    let flags := ks.flatMap fun k => match (E[k]? : Option WExpr) with
      | some (WExpr.lit c0) =>
        (List.range 2).filterMap (fun c1 => if c1 ≠ c0 % W ∧ setsTo li k c1 then some c1 else none)
          |>.flatMap fun c1 => F.or (.eq (hw n k) (.lit c0)) (.eq (hw n k) (.lit c1)) ::
            step.filterMap fun j => (E[j]?).map fun ej => F.or (.not (.eq (hw n k) (.lit c0))) (.eq (hw n j) ej)
      | _ => []
    (call ++ same ++ rel ++ left ++ bnd ++ flags).eraseDups

def measures (n : Nat) (li : List (Facts × Out)) : List WExpr :=
  let a : List WExpr := (exitTests n li).filterMap fun (t : Nat × WExpr) =>
    if steps n li t.1 1 then some (WExpr.bin .sub t.2 (hw n t.1)) else none
  let b : List WExpr := (nzTests n li).filterMap fun k =>
    if steps n li k 1 then some (WExpr.bin .sub (.lit 0) (hw n k)) else none
  (a ++ b).eraseDups

def houdini (n : Nat) (le li : List (Facts × Out)) : Nat → List F → List F
  | 0, fs => fs
  | k + 1, fs =>
    let keep := fs.filter (holdsAfter n le li fs)
    if keep.length = fs.length then fs else houdini n le li k keep

/-- The inferred invariant. -/
def infer (n nhw : Nat) (le li : List (Facts × Out)) : List F :=
  houdini n le li (nhw + 8) (cands n nhw le li)

end Verify.LoopSource.Equiv.Inv

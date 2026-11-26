import Verify.VC.Check
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A verified decision procedure for solar-verify's scripts

`dischargeScript cs` decides, by evaluation in the kernel, that every obligation of the script
`cs` (the facts one `check-sat` reads, `obligations`) has no model, leaving out the probes
(`isProbe`); `dischargeScript_sound` shows that `dischargeScript cs = true` gives `Valid cs`,
the claim of solar-verify's verdict, with no solver and no certificate. The procedure is
incomplete and fails closed: an obligation it cannot refute makes it answer `false`.

For one obligation (`refuteOb`):

1. Definitions: every fact `(= x u)` with `x` a constant is an equation; each constant with
   one is replaced by its term, to a bounded depth, outside quantifiers (`substN`). Every model
   of the facts satisfies the equations, so it satisfies the rewritten facts (`substN_eval`).
2. A tableau (`refute`): conjunctions are split into facts, disjunctions, implications and negated
   conjunctions into branches (each of which must close), and an `ite` of integers that is an
   argument of a comparison into its two cases (`splitIte`). A comparison of linear terms
   (`lin`: numerals, `+`, `-`, multiplication by a numeral, and any other integer term as
   an atom compared by syntax) becomes constraints `l ≤ 0` (`cmpCons`, `x < y` read as
   `x - y + 1 ≤ 0` over the integers); a disequality of integers is split in two. Every other
   fact is dropped, which is sound.
3. Fourier-Motzkin (`fm`): a branch closes when eliminating its constants one at a time, by
   nonnegative combinations of pairs of constraints, reaches a constraint `k ≤ 0` with `0 < k`.

Each step is proved sound once (`step_sound`, `elim_sound`, `fm_sound`), whatever the terms
are; fuel bounds every recursion, so the kernel evaluates the procedure by structural recursion.
-/

namespace SolidCore.Verify.VC

/-! ## Linear forms -/

/-- `k + Σ c * t`, over integer terms `t`. -/
structure Lin where
  k : Int
  cs : List (Tm × Int)

noncomputable def sumCs (σ : Env) : List (Tm × Int) → Int
  | [] => 0
  | p :: ps => p.2 * (p.1.eval σ).toInt + sumCs σ ps

noncomputable def Lin.eval (σ : Env) (l : Lin) : Int := l.k + sumCs σ l.cs

def Lin.add (a b : Lin) : Lin := ⟨a.k + b.k, a.cs ++ b.cs⟩
def Lin.scale (c : Int) (a : Lin) : Lin := ⟨c * a.k, a.cs.map fun p => (p.1, c * p.2)⟩
def Lin.sub (a b : Lin) : Lin := a.add (b.scale (-1))
def Lin.inc (a : Lin) : Lin := ⟨a.k + 1, a.cs⟩

/-- Add one monomial to a list, merging it with one of the same term. -/
def insertC (p : Tm × Int) : List (Tm × Int) → List (Tm × Int)
  | [] => [p]
  | q :: qs => if Tm.beq q.1 p.1 then (q.1, q.2 + p.2) :: qs else q :: insertC p qs

/-- Merge the monomials of one term and drop those with coefficient 0. -/
def Lin.norm (a : Lin) : Lin := ⟨a.k, (a.cs.foldr insertC []).filter fun p => p.2 != 0⟩

/-- The coefficient of a term in a merged form. -/
def coeff (a : Lin) (x : Tm) : Int :=
  match a.cs.find? (fun p => Tm.beq p.1 x) with
  | some p => p.2
  | none => 0

/-! ## Fourier-Motzkin -/

/-- Eliminate `x` from constraints `l ≤ 0`: keep those without it and add, for each pair with
coefficients of opposite signs, their combination in which it cancels. -/
def elim (x : Tm) (cs : List Lin) : List Lin :=
  let pos := cs.filter fun l => decide (0 < coeff l x)
  let neg := cs.filter fun l => decide (coeff l x < 0)
  cs.filter (fun l => decide (coeff l x = 0)) ++
    pos.flatMap fun p => neg.map fun q => ((p.scale (-(coeff q x))).add (q.scale (coeff p x))).norm

/-- How many constraints eliminating `x` adds: pairs of opposite signs. -/
def elimCost (cs : List Lin) (x : Tm) : Nat :=
  (cs.filter fun l => decide (0 < coeff l x)).length * (cs.filter fun l => decide (coeff l x < 0)).length

/-- The term of the constraints whose elimination adds the fewest. -/
def pickVar (cs : List Lin) : Option Tm :=
  (cs.flatMap fun l => l.cs.map (·.1)).foldl (fun best x => match best with
    | none => some x
    | some y => if elimCost cs x < elimCost cs y then some x else some y) none

/-- Whether the constraints `l ≤ 0` have no integer solution, by Fourier-Motzkin with `fuel`
eliminations. -/
def fm : Nat → List Lin → Bool
  | 0, _ => false
  | n + 1, cs =>
    let cs := cs.filter fun l => !(l.cs.isEmpty && decide (l.k ≤ 0))
    if cs.any (fun l => l.cs.isEmpty && decide (0 < l.k)) then true
    else match pickVar cs with
      | none => false
      | some x => if elimCost cs x ≤ 256 ∧ cs.length ≤ 512 then fm n (elim x cs) else false

/-! ## Linear terms -/

def Tm.isIntAtom (t : Tm) : Bool := t.sort? == some .int

/-- An integer term as an atom of a linear form. -/
def linAtom (t : Tm) : Option Lin := if t.isIntAtom then some ⟨0, [(t, 1)]⟩ else none

/-- The linear form of an integer term, with `fuel` levels. -/
def lin : Nat → Tm → Option Lin
  | 0, _ => none
  | n + 1, t =>
    match t with
    | .num m => some ⟨m, []⟩
    | .app f args =>
      if f = "+" then
        match args with
        | [a, b] => match lin n a, lin n b with
          | some la, some lb => some (la.add lb)
          | _, _ => none
        | _ => none
      else if f = "-" then
        match args with
        | [a] => (lin n a).map (Lin.scale (-1))
        | [a, b] => match lin n a, lin n b with
          | some la, some lb => some (la.sub lb)
          | _, _ => none
        | _ => none
      else if f = "*" then
        match args with
        | [.num c, a] => (lin n a).map (Lin.scale c)
        | [a, .num c] => (lin n a).map (Lin.scale c)
        | _ => linAtom t
      else linAtom t
    | _ => linAtom t

/-- The constraints `l ≤ 0` a comparison `f` of `a` and `b` (negated when `pos` is false) gives. -/
def cmpCons (f : String) (pos : Bool) (a b : Lin) : List Lin :=
  if f = "<=" then (if pos then [a.sub b] else [(b.sub a).inc])
  else if f = "<" then (if pos then [(a.sub b).inc] else [b.sub a])
  else if f = ">=" then (if pos then [b.sub a] else [(a.sub b).inc])
  else if f = ">" then (if pos then [(b.sub a).inc] else [a.sub b])
  else if f = "=" then (if pos then [a.sub b, b.sub a] else [])
  else []

/-! ## Definitions -/

def Tm.isConst : Tm → Bool
  | .ivar _ | .bvar _ | .avar _ | .a2var _ => true
  | _ => false

/-- `(= x u)` with `x` a constant. -/
def eqOf? : Tm → Option (Tm × Tm)
  | .app f [v, u] => if f = "=" ∧ v.isConst = true then some (v, u) else none
  | _ => none

def lookupEq : List (Tm × Tm) → Tm → Option Tm
  | [], _ => none
  | e :: es, v => if Tm.beq e.1 v then some e.2 else lookupEq es v

/-- Replace each constant with an equation by its term, `n` levels deep, outside quantifiers. -/
def substN : List (Tm × Tm) → Nat → Tm → Tm
  | _, 0, t => t
  | eqs, n + 1, t =>
    match t with
    | .app f args => .app f (args.map (substN eqs n))
    | .all x body =>
      .all x (substN (eqs.filter fun e => !(e.1.vars.contains x || e.2.vars.contains x)) n body)
    | t => if t.isConst then (match lookupEq eqs t with | some u => substN eqs n u | none => t) else t

/-! ## The tableau -/

def neg (t : Tm) : Tm := .app "not" [t]
def wrap (pos : Bool) (t : Tm) : Tm := if pos then t else neg t

/-- `(ite c p q)` with `p` and `q` integers. -/
def isIte : Tm → Option (Tm × Tm × Tm)
  | .app g [c, p, q] => if g = "ite" ∧ p.isIntAtom = true ∧ q.isIntAtom = true then some (c, p, q) else none
  | _ => none

/-- The first of `args` in which `g` finds an `ite`, with the two cases of the list. -/
def liftArgs (g : Tm → Option (Tm × Tm × Tm)) : List Tm → Option (Tm × List Tm × List Tm)
  | [] => none
  | a :: as =>
    match g a with
    | some (c, a1, a2) => some (c, a1 :: as, a2 :: as)
    | none => (liftArgs g as).map fun r => (r.1, a :: r.2.1, a :: r.2.2)

/-- The leftmost integer `ite` of a term, outside quantifiers, as its condition and the term with
the `ite` replaced by each of its cases. -/
def liftIte : Nat → Tm → Option (Tm × Tm × Tm)
  | 0, _ => none
  | n + 1, t =>
    match t with
    | .app f args =>
      match isIte t with
      | some r => some r
      | none => (liftArgs (liftIte n) args).map fun r => (r.1, .app f r.2.1, .app f r.2.2)
    | _ => none

/-- What one fact gives the tableau. -/
inductive Step where
  | drop
  | closed
  | facts (ts : List Tm)
  | cons (ls : List Lin)
  | split (bs : List (List Tm))
  /-- `c` and `t1`, or the negation of `c` and `t2`: the cases of an `ite` on `c`. -/
  | ite (c t1 t2 : Tm)
  /-- `t`, at some value of the constant `x`: a negated quantifier, opened at a witness. -/
  | skolem (x : String) (t : Tm)

def linFuel : Nat := 64

def isCmp (f : String) : Bool := f == "<=" || f == "<" || f == ">=" || f == ">" || f == "="

/-- A comparison `f a b`, asserted (`pos`) or negated. -/
def atomStep (pos : Bool) (f : String) (a b : Tm) : Step :=
  match liftIte linFuel (.app f [a, b]) with
  | some (c, t1, t2) => .ite c (wrap pos t1) (wrap pos t2)
  | none =>
    match lin linFuel a, lin linFuel b with
    | some la, some lb =>
      if f = "=" ∧ pos = false then .split [[.app "<" [a, b]], [.app "<" [b, a]]]
      else .cons ((cmpCons f pos la lb).map Lin.norm)
    | _, _ => .drop

def stepNot (x : Tm) : Step :=
  match x with
  | .tt => .closed
  | .ff => .drop
  | .app f args =>
    if f = "not" then (match args with | [a] => .facts [a] | _ => .drop)
    else if f = "and" then .split (args.map fun a => [neg a])
    else if f = "or" then .facts (args.map neg)
    else if f = "=>" then (match args with | [a, b] => .facts [a, neg b] | _ => .drop)
    else if isCmp f then (match args with | [a, b] => atomStep false f a b | _ => .drop)
    else .drop
  | .all x body => .skolem x (neg body)
  | _ => .drop

/-- The instances of `(forall ((x Int)) body)` at the integer constants `ks` (the goal's
quantified variables, opened as constants by `skolem`), leaving out a constant `body` binds. -/
def instances (ks : List String) (x : String) (body : Tm) : List Tm :=
  ks.filterMap fun k => if body.binders.contains k then none else some (body.subst .int x (.ivar k))

def step (ks : List String) (t : Tm) : Step :=
  match t with
  | .tt => .drop
  | .ff => .closed
  | .app f args =>
    if f = "and" then .facts args
    else if f = "or" then .split (args.map fun a => [a])
    else if f = "=>" then (match args with | [a, b] => .split [[neg a], [b]] | _ => .drop)
    else if f = "not" then (match args with | [x] => stepNot x | _ => .drop)
    else if isCmp f then (match args with | [a, b] => atomStep true f a b | _ => .drop)
    else .drop
  | .all x body => .facts (instances ks x body)
  | _ => .drop

/-- The constant `x` occurs in none of the facts `rest` and the constraints `cs`. -/
def fresh (x : String) (rest : List Tm) (cs : List Lin) : Bool :=
  rest.all (fun u => !u.vars.contains x) && cs.all (fun l => l.cs.all fun p => !p.1.vars.contains x)

/-- Replace every integer `ite` on the condition `c` by its case `b`, `n` levels deep, outside
quantifiers. -/
def resolve (c : Tm) (b : Bool) : Nat → Tm → Tm
  | 0, t => t
  | n + 1, t =>
    match t with
    | .app f args =>
      let t' := Tm.app f (args.map (resolve c b n))
      match isIte t' with
      | some (c', p, q) => if Tm.beq c' c then (if b then p else q) else t'
      | none => t'
    | t => t

def resolveFuel : Nat := 64

def substFuel : Nat := 128

/-- The equation a case `c` of an `ite` gives, when it is `(= a b)` of integers with `a` (or `b`) a
constant: in the case where `c` holds, the constant is replaced by the other side. -/
def iteEqs (c : Tm) : List (Tm × Tm) :=
  match c with
  | .app f [a, b] =>
    if f = "=" ∧ a.isIntAtom = true ∧ b.isIntAtom = true then
      (if a.isConst then [(a, b)] else if b.isConst then [(b, a)] else [])
    else []
  | _ => []

/-- Whether the facts `ts` and the constraints `cs` have no common model, with `n` steps on each
branch, at most `b` nested case splits, and `F` eliminations at the end of each branch. -/
def refute (F : Nat) (ks : List String) : Nat → Nat → List Tm → List Lin → Bool
  | 0, _, _, _ => false
  | _ + 1, _, [], cs => fm F cs
  | n + 1, b, t :: rest, cs =>
    match step ks t with
    | .drop => refute F ks n b rest cs
    | .closed => true
    | .facts ts => refute F ks n b (ts ++ rest) cs
    | .cons ls => refute F ks n b rest (ls ++ cs)
    | .split bs => fm F cs || (b != 0 && bs.all fun ts => refute F ks n (b - 1) (ts ++ rest) cs)
    | .ite c t1 t2 =>
      fm F cs || b != 0 && (refute F ks n (b - 1)
          (c :: ((t1 :: rest).map (resolve c true resolveFuel)).map (substN (iteEqs c) substFuel)) cs &&
        refute F ks n (b - 1) (neg c :: (t2 :: rest).map (resolve c false resolveFuel)) cs)
    | .skolem x t =>
      if fresh x rest cs then refute F ks n b (t :: rest) cs
      else if fresh (x ++ "'") (t :: rest) cs then
        refute F ks n b (t.subst .int x (.ivar (x ++ "'")) :: rest) cs
      else refute F ks n b rest cs

/-! ## Arrays -/

/-- `(store a i v)` of an array of integers or of a mapping of mappings. -/
def rowSorts (a v : Tm) : Bool :=
  (a.sort? == some .arr && v.isIntAtom) || (a.sort? == some .arr2 && v.sort? == some .arr)

/-- Two arrays of one sort. -/
def arrPair (p q : Tm) : Bool :=
  (p.sort? == some .arr && q.sort? == some .arr) || (p.sort? == some .arr2 && q.sort? == some .arr2)

/-- One step at `(select x j)`, `x` and `j` rewritten: read over write (`v` itself when `j` and `i`
are one term), a read of an `ite` of arrays as the `ite` of its reads, and a read of a constant
array. `r` rewrites the new reads. -/
def rowSel (r : Tm → Tm) (x j : Tm) : Tm :=
  match x with
  | .app g [a, i, v] =>
    if g = "store" ∧ i.isIntAtom = true ∧ j.isIntAtom = true ∧ rowSorts a v = true then
      (if Tm.beq j i then v else .app "ite" [.app "=" [j, i], v, r (.app "select" [a, j])])
    else if g = "ite" ∧ arrPair i v = true then
      .app "ite" [a, r (.app "select" [i, j]), r (.app "select" [v, j])]
    else .app "select" [x, j]
  | .app g [v] =>
    if (g = isOpName.constName ∧ v.isIntAtom = true) ∨ (g = isOpName.const2Name ∧ v.sort? = some .arr)
    then v else .app "select" [x, j]
  | _ => .app "select" [x, j]

/-- Read over write, inside out, `n` levels deep, outside quantifiers (`rowSel`). -/
def rowN : Nat → Tm → Tm
  | 0, t => t
  | n + 1, t =>
    match t with
    | .app f args =>
      let args' := args.map (rowN n)
      if f = "select" then
        match args' with
        | [x, j] => rowSel (rowN n) x j
        | _ => .app f args'
      else .app f args'
    | .all x body => .all x (rowN n body)
    | t => t

def rowFuel : Nat := 64

/-! ## The procedure -/

def stepFuel : Nat := 4096
def splitFuel : Nat := 48
def fmFuel : Nat := 256

/-- The constants reachable from `xs` through facts that share one, in `n` rounds. -/
def reach (fs : List Tm) : Nat → List String → List String
  | 0, xs => xs
  | n + 1, xs => reach fs n ((fs.filter fun t => t.vars.any xs.contains).flatMap Tm.vars ++ xs)

/-- Keep the facts that mention a constant reachable from the last fact's (the negated goal's),
and those that mention none. Dropping facts is sound: a model of all of them is one of these. -/
def relevant (fs : List Tm) : List Tm :=
  let xs := reach fs 3 ((fs.getLast?.map Tm.vars).getD [])
  fs.filter fun t => t.vars.isEmpty || t.vars.any xs.contains

mutual
/-- The terms `(mod t M)` and `(div t M)` with `M` a positive numeral, outside quantifiers, as
`(t, M)`. -/
def Tm.mods : Tm → List (Tm × Nat)
  | .app f args =>
    (match f, args with
      | "mod", [t, .num m] => if 0 < m then [(t, m)] else []
      | "div", [t, .num m] => if 0 < m then [(t, m)] else []
      | _, _ => []) ++ Tm.modsList args
  | _ => []
def Tm.modsList : List Tm → List (Tm × Nat)
  | [] => []
  | t :: ts => Tm.mods t ++ Tm.modsList ts
end

/-- What every model gives `(mod t M)` and `(div t M)`, for `0 < M`: `t = M * (div t M) + (mod t M)`
and `0 ≤ (mod t M) ≤ M - 1`, and the integer `(div t M)` is at most -1, 0 or at least 1 (the
cases that let Fourier-Motzkin, over the rationals, see that it is an integer). -/
def modFacts (t : Tm) (m : Nat) : List Tm :=
  let r := Tm.app "mod" [t, .num m]
  let q := Tm.app "div" [t, .num m]
  [.app "=" [t, .app "+" [.app "*" [.num m, q], r]], .app "<=" [.num 0, r], .app "<=" [r, .num (m - 1)],
    .app "or" [.app "<=" [.app "+" [q, .num 1], .num 0], .app "=" [q, .num 0], .app "<=" [.num 1, q]]]

/-- The facts of every `mod` and `div` by a positive numeral in `fs`. -/
def divFacts (fs : List Tm) : List Tm :=
  ((Tm.modsList fs).foldl (fun acc p => if acc.any (fun q => q.2 == p.2 && Tm.beq q.1 p.1) then acc
    else acc ++ [p]) []).flatMap fun p =>
      if p.1.isIntAtom = true ∧ 0 < p.2 then modFacts p.1 p.2 else []

/-- The last fact (the negated goal) first, so that its quantifiers are opened before the facts that
are instantiated at them. -/
def goalFirst (fs : List Tm) : List Tm := fs.getLast?.toList ++ fs.dropLast

mutual
/-- The integer constants a term reads or writes an array at, outside quantifiers. -/
def Tm.selIdx : Tm → List String
  | .app f args =>
    (match f, args with
      | "select", [_, .ivar x] => [x]
      | "store", [_, .ivar x, _] => [x]
      | _, _ => []) ++ Tm.selIdxList args
  | _ => []
def Tm.selIdxList : List Tm → List String
  | [] => []
  | t :: ts => Tm.selIdx t ++ Tm.selIdxList ts
end

/-- The constants the facts' quantifiers are instantiated at: the variables the goal quantifies
(opened as constants first, or under a primed name when the plain one is taken) and the integer
constants the facts index arrays at. -/
def goalBinders (fs : List Tm) : List String :=
  let bs := (fs.getLast?.map Tm.binders).getD []
  (bs ++ bs.map (· ++ "'") ++ Tm.selIdxList fs).foldl
    (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Whether one obligation's facts have no model: its equations are substituted, and dropped, the
facts the goal does not reach are left out, and the goal comes first. -/
def refuteOb (fs : List Tm) : Bool :=
  let eqs := fs.filterMap eqOf?
  let gs := (fs.filter fun t => (eqOf? t).isNone).map fun t => rowN rowFuel (substN eqs substFuel t)
  let rs := relevant gs
  refute fmFuel (goalBinders rs) stepFuel splitFuel (goalFirst rs) [] ||
    refute fmFuel (goalBinders rs) stepFuel splitFuel (goalFirst rs ++ divFacts rs) []

/-- Whether every obligation of a script but the probes has no model. -/
def dischargeScript (cs : List Cmd) : Bool :=
  (obligations cs).all fun fs => isProbe fs || refuteOb fs

/-- Whether the obligation at index `i` of a script is a probe or has no model: one kernel check
per obligation keeps each evaluation small (`dischargeScript_of_each`). -/
def dischargeAt (cs : List Cmd) (i : Nat) : Bool :=
  let fs := (obligations cs).getD i []
  isProbe fs || refuteOb fs

end SolidCore.Verify.VC

/-! ## Soundness -/

namespace SolidCore.Verify.VC

section Sound

variable (σ : Env)

theorem sumCs_append (l m : List (Tm × Int)) : sumCs σ (l ++ m) = sumCs σ l + sumCs σ m := by
  induction l with
  | nil => simp [sumCs]
  | cons p ps ih => simp only [List.cons_append, sumCs, ih]; ring

theorem sumCs_scale (c : Int) (l : List (Tm × Int)) :
    sumCs σ (l.map fun p => (p.1, c * p.2)) = c * sumCs σ l := by
  induction l with
  | nil => simp [sumCs]
  | cons p ps ih => simp only [List.map_cons, sumCs, ih]; ring

theorem Lin.eval_add (a b : Lin) : (a.add b).eval σ = a.eval σ + b.eval σ := by
  simp only [Lin.add, Lin.eval, sumCs_append]; ring

theorem Lin.eval_scale (c : Int) (a : Lin) : (a.scale c).eval σ = c * a.eval σ := by
  simp only [Lin.scale, Lin.eval, sumCs_scale]; ring

theorem Lin.eval_sub (a b : Lin) : (a.sub b).eval σ = a.eval σ - b.eval σ := by
  simp only [Lin.sub, Lin.eval_add, Lin.eval_scale]; ring

theorem Lin.eval_inc (a : Lin) : a.inc.eval σ = a.eval σ + 1 := by
  simp only [Lin.inc, Lin.eval]; ring

theorem sumCs_insertC (p : Tm × Int) (qs : List (Tm × Int)) :
    sumCs σ (insertC p qs) = p.2 * (p.1.eval σ).toInt + sumCs σ qs := by
  induction qs with
  | nil => simp [insertC, sumCs]
  | cons q qs ih =>
    simp only [insertC]
    split
    · rename_i h
      have := Tm.eq_of_beq h
      simp only [sumCs, this]; ring
    · simp only [sumCs, ih]; ring

theorem sumCs_foldr (l : List (Tm × Int)) : sumCs σ (l.foldr insertC []) = sumCs σ l := by
  induction l with
  | nil => simp [sumCs]
  | cons p ps ih => simp only [List.foldr_cons, sumCs_insertC, ih, sumCs]

theorem sumCs_filter (l : List (Tm × Int)) :
    sumCs σ (l.filter fun p => p.2 != 0) = sumCs σ l := by
  induction l with
  | nil => simp [sumCs]
  | cons p ps ih =>
    by_cases h : p.2 = 0
    · simp [h, sumCs, ih]
    · simp [h, sumCs, ih]

theorem Lin.eval_norm (a : Lin) : a.norm.eval σ = a.eval σ := by
  simp only [Lin.norm, Lin.eval, sumCs_filter, sumCs_foldr]

/-! ### Fourier-Motzkin -/

theorem elim_sound (x : Tm) (cs : List Lin) (h : ∀ l ∈ cs, l.eval σ ≤ 0) :
    ∀ l ∈ elim x cs, l.eval σ ≤ 0 := by
  intro l hl
  simp only [elim, List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map] at hl
  rcases hl with ⟨hl, _⟩ | ⟨p, ⟨hp, hpx⟩, q, ⟨hq, hqx⟩, rfl⟩
  · exact h l hl
  · rw [Lin.eval_norm, Lin.eval_add, Lin.eval_scale, Lin.eval_scale]
    have h1 := h p hp
    have h2 := h q hq
    simp only [decide_eq_true_eq] at hpx hqx
    nlinarith

theorem fm_sound : ∀ (n : Nat) (cs : List Lin), fm n cs = true → (∀ l ∈ cs, l.eval σ ≤ 0) → False
  | 0, _, h, _ => by simp [fm] at h
  | n + 1, cs, h, hc => by
    have hc' : ∀ l ∈ cs.filter (fun l => !(l.cs.isEmpty && decide (l.k ≤ 0))), l.eval σ ≤ 0 :=
      fun l hl => hc l (List.mem_filter.mp hl).1
    simp only [fm] at h
    generalize cs.filter (fun l => !(l.cs.isEmpty && decide (l.k ≤ 0))) = ds at h hc'
    split at h
    · rename_i hany
      obtain ⟨l, hl, hk⟩ := List.any_eq_true.mp hany
      simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hk
      have := hc' l hl
      simp only [Lin.eval, hk.1, sumCs] at this
      omega
    · split at h
      · simp at h
      · split at h
        · exact fm_sound n _ h (elim_sound σ _ _ hc')
        · simp at h

/-! ### Terms -/

theorem eval_app (f : String) (args : List Tm) :
    (Tm.app f args).eval σ = applyOp σ.u f (args.map (Tm.eval σ)) := by
  simp [Tm.eval, Tm.evalList_eq]

theorem holds_app (f : String) (args : List Tm) :
    (Tm.app f args).Holds σ = (applyOp σ.u f (args.map (Tm.eval σ))).toProp := by
  simp [Tm.Holds, eval_app]

theorem eval_num (n : Nat) : (Tm.num n).eval σ = .int n := by simp [Tm.eval]

theorem holds_neg (t : Tm) : (neg t).Holds σ ↔ ¬ t.Holds σ := by
  rw [neg, holds_app]; simp [applyOp, Value.toProp, Tm.Holds]

theorem holds_and (args : List Tm) : (Tm.app "and" args).Holds σ ↔ ∀ a ∈ args, a.Holds σ := by
  rw [holds_app]; simp [applyOp, Value.toProp, Tm.Holds]

theorem holds_or (args : List Tm) : (Tm.app "or" args).Holds σ ↔ ∃ a ∈ args, a.Holds σ := by
  rw [holds_app]; simp [applyOp, Value.toProp, Tm.Holds]

theorem holds_imp (a b : Tm) : (Tm.app "=>" [a, b]).Holds σ ↔ (a.Holds σ → b.Holds σ) := by
  rw [holds_app]; simp [applyOp, Value.toProp, Tm.Holds]

theorem int_atom {t : Tm} (h : t.isIntAtom = true) : t.eval σ = .int (t.eval σ).toInt := by
  simp only [Tm.isIntAtom, beq_iff_eq] at h
  exact Value.sortOf_int (Tm.eval_sortOf t σ h)

theorem linAtom_sound {t : Tm} {l : Lin} (h : linAtom t = some l) : t.eval σ = .int (l.eval σ) := by
  unfold linAtom at h
  split_ifs at h with ha
  simp only [Option.some.injEq] at h
  subst h
  rw [int_atom σ ha]
  simp [Lin.eval, sumCs]

theorem lin_sound : ∀ (n : Nat) (t : Tm) (l : Lin), lin n t = some l → t.eval σ = .int (l.eval σ)
  | 0, _, _, h => by simp [lin] at h
  | n + 1, t, l, h => by
    unfold lin at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [eval_num, Lin.eval, sumCs]
    · rename_i f args
      split_ifs at h with h1 h2 h3
      · subst h1
        split at h
        · rename_i a b
          split at h
          · rename_i la lb ha hb
            simp only [Option.some.injEq] at h
            subst h
            simp [eval_app, applyOp, lin_sound n a la ha, lin_sound n b lb hb, Value.toInt,
              Lin.eval_add]
          · simp at h
        · simp at h
      · subst h2
        split at h
        · rename_i a
          obtain ⟨la, ha, rfl⟩ := Option.map_eq_some_iff.mp h
          simp [eval_app, applyOp, lin_sound n a la ha, Value.toInt, Lin.eval_scale]
        · rename_i a b
          split at h
          · rename_i la lb ha hb
            simp only [Option.some.injEq] at h
            subst h
            simp [eval_app, applyOp, lin_sound n a la ha, lin_sound n b lb hb, Value.toInt,
              Lin.eval_sub]
          · simp at h
        · simp at h
      · subst h3
        split at h
        · rename_i c a
          obtain ⟨la, ha, rfl⟩ := Option.map_eq_some_iff.mp h
          simp [eval_app, applyOp, lin_sound n a la ha, Value.toInt, Lin.eval_scale, eval_num]
        · rename_i a c _
          obtain ⟨la, ha, rfl⟩ := Option.map_eq_some_iff.mp h
          simp [eval_app, applyOp, lin_sound n a la ha, Value.toInt, Lin.eval_scale, eval_num]
          ring
        · exact linAtom_sound σ h
      · exact linAtom_sound σ h
    · exact linAtom_sound σ h

theorem holds_wrap_congr {pos : Bool} {X Y : Tm} (he : X.eval σ = Y.eval σ)
    (h : (wrap pos X).Holds σ) : (wrap pos Y).Holds σ := by
  cases pos
  · simp only [wrap, holds_neg, Bool.false_eq_true, ↓reduceIte] at h ⊢
    simpa [Tm.Holds, he] using h
  · simp only [wrap, ↓reduceIte] at h ⊢
    simpa [Tm.Holds, he] using h

theorem isIte_sound {t c p q : Tm} (h : isIte t = some (c, p, q)) :
    (c.Holds σ → t.eval σ = p.eval σ) ∧ (¬ c.Holds σ → t.eval σ = q.eval σ) := by
  unfold isIte at h
  split at h
  · rename_i g c' p' q'
    split_ifs at h with hg
    obtain ⟨rfl, hp, hq⟩ := hg
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨x, hx⟩ : ∃ x, p'.eval σ = .int x := ⟨_, int_atom σ hp⟩
    obtain ⟨y, hy⟩ : ∃ y, q'.eval σ = .int y := ⟨_, int_atom σ hq⟩
    refine ⟨fun hc => ?_, fun hc => ?_⟩ <;>
      simp only [Tm.Holds] at hc <;> simp [eval_app, hx, hy, applyOp, hc]
  · simp at h

theorem liftArgs_sound {g : Tm → Option (Tm × Tm × Tm)}
    (hg : ∀ t c t1 t2, g t = some (c, t1, t2) →
      (c.Holds σ → t.eval σ = t1.eval σ) ∧ (¬ c.Holds σ → t.eval σ = t2.eval σ)) :
    ∀ (args : List Tm) {c : Tm} {l1 l2 : List Tm}, liftArgs g args = some (c, l1, l2) →
      (c.Holds σ → args.map (Tm.eval σ) = l1.map (Tm.eval σ)) ∧
        (¬ c.Holds σ → args.map (Tm.eval σ) = l2.map (Tm.eval σ))
  | [], _, _, _, h => by simp [liftArgs] at h
  | a :: as, c, l1, l2, h => by
    simp only [liftArgs] at h
    split at h
    · rename_i c' a1 a2 ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := hg a _ _ _ ha
      exact ⟨fun hc => by simp [h1 hc], fun hc => by simp [h2 hc]⟩
    · obtain ⟨⟨c', r1, r2⟩, hr, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := liftArgs_sound hg as hr
      exact ⟨fun hc => by simp [h1 hc], fun hc => by simp [h2 hc]⟩

theorem liftIte_sound : ∀ (n : Nat) (t c t1 t2 : Tm), liftIte n t = some (c, t1, t2) →
    (c.Holds σ → t.eval σ = t1.eval σ) ∧ (¬ c.Holds σ → t.eval σ = t2.eval σ)
  | 0, _, _, _, _, h => by simp [liftIte] at h
  | n + 1, t, c, t1, t2, h => by
    unfold liftIte at h
    split at h
    · rename_i f args
      split at h
      · rename_i r hi
        simp only [Option.some.injEq] at h
        subst h
        exact isIte_sound σ hi
      · obtain ⟨⟨c', r1, r2⟩, hr, h⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := liftArgs_sound σ (liftIte_sound n) args hr
        exact ⟨fun hc => by simp only [eval_app, h1 hc], fun hc => by simp only [eval_app, h2 hc]⟩
    · simp at h

theorem cmpCons_sound (f : String) (pos : Bool) {a b : Tm} {la lb : Lin}
    (ha : a.eval σ = .int (la.eval σ)) (hb : b.eval σ = .int (lb.eval σ))
    (h : (wrap pos (.app f [a, b])).Holds σ) : ∀ l ∈ cmpCons f pos la lb, l.eval σ ≤ 0 := by
  intro l hl
  have hx : (Tm.app f [a, b]).Holds σ =
      (applyOp σ.u f [.int (la.eval σ), .int (lb.eval σ)]).toProp := by
    rw [holds_app]; simp [ha, hb]
  have hw : (wrap pos (.app f [a, b])).Holds σ ↔
      (if pos then (applyOp σ.u f [.int (la.eval σ), .int (lb.eval σ)]).toProp
       else ¬ (applyOp σ.u f [.int (la.eval σ), .int (lb.eval σ)]).toProp) := by
    cases pos <;> simp [wrap, holds_neg, hx]
  rw [hw] at h
  unfold cmpCons at hl
  split_ifs at hl h <;> subst_vars <;>
    simp [applyOp, Value.toProp, Value.toInt, Value.eq] at h hl <;>
    (try rcases hl with rfl | rfl) <;> (try subst hl) <;> simp only [Lin.eval_sub, Lin.eval_inc] <;> omega

/-- What a step of the tableau may assume of one fact's model. -/
def StepOK : Step → Prop
  | .drop => True
  | .closed => False
  | .facts ts => ∀ u ∈ ts, u.Holds σ
  | .cons ls => ∀ l ∈ ls, l.eval σ ≤ 0
  | .split bs => ∃ ts ∈ bs, ∀ u ∈ ts, u.Holds σ
  | .ite c t1 t2 => (c.Holds σ ∧ t1.Holds σ) ∨ (¬ c.Holds σ ∧ t2.Holds σ)
  | .skolem x t => ∃ m : Int, t.Holds (σ.setI x m)

theorem atomStep_sound (pos : Bool) (f : String) (a b : Tm)
    (h : (wrap pos (.app f [a, b])).Holds σ) : StepOK σ (atomStep pos f a b) := by
  unfold atomStep
  split
  · rename_i c t1 t2 hs
    obtain ⟨h1, h2⟩ := liftIte_sound σ _ _ _ _ _ hs
    by_cases hc : c.Holds σ
    · exact Or.inl ⟨hc, holds_wrap_congr σ (h1 hc) h⟩
    · exact Or.inr ⟨hc, holds_wrap_congr σ (h2 hc) h⟩
  · split
    · rename_i la lb hla hlb
      have ha := lin_sound σ _ _ _ hla
      have hb := lin_sound σ _ _ _ hlb
      split_ifs with he
      · obtain ⟨rfl, rfl⟩ := he
        simp only [wrap, holds_neg, holds_app, List.map_cons, List.map_nil, ha, hb,
          Bool.false_eq_true, ↓reduceIte] at h
        simp only [applyOp, Value.toProp, Value.eq] at h
        rcases lt_or_gt_of_ne h with h | h
        · exact ⟨[.app "<" [a, b]], by simp, by
            simp [holds_app, ha, hb, applyOp, Value.toProp, Value.toInt, h]⟩
        · exact ⟨[.app "<" [b, a]], by simp, by
            simp [holds_app, ha, hb, applyOp, Value.toProp, Value.toInt, h]⟩
      · intro l hl
        simp only [List.mem_map] at hl
        obtain ⟨l', hl', rfl⟩ := hl
        rw [Lin.eval_norm]
        exact cmpCons_sound σ f pos ha hb h l' hl'
    · trivial

theorem stepNot_sound (x : Tm) (h : ¬ x.Holds σ) : StepOK σ (stepNot x) := by
  unfold stepNot
  split
  · exact h (by simp [Tm.Holds, Tm.eval, Value.toProp])
  · trivial
  · rename_i f args
    split_ifs with h1 h2 h3 h4 h5
    · subst h1
      split
      · rename_i a
        have : ¬ (neg a).Holds σ := h
        rw [holds_neg] at this
        intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        subst hu
        exact Classical.not_not.mp this
      · trivial
    · subst h2
      rw [holds_and] at h
      push Not at h
      obtain ⟨a, ha, hna⟩ := h
      exact ⟨[neg a], List.mem_map.mpr ⟨a, ha, rfl⟩, by simp [holds_neg, hna]⟩
    · subst h3
      rw [holds_or] at h
      push Not at h
      intro u hu
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
      exact (holds_neg σ a).mpr (h a ha)
    · subst h4
      split
      · rename_i a b
        rw [holds_imp] at h
        push Not at h
        intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl
        · exact h.1
        · exact (holds_neg σ b).mpr h.2
      · trivial
    · split
      · rename_i a b
        exact atomStep_sound σ false f a b (by simpa [wrap, holds_neg] using h)
      · trivial
    · trivial
  · rename_i x body
    have h' : ¬ ∀ m : Int, body.Holds (σ.setI x m) := h
    push Not at h'
    obtain ⟨m, hm⟩ := h'
    exact ⟨m, (holds_neg _ body).mpr hm⟩
  · trivial

theorem step_sound (ks : List String) (t : Tm) (h : t.Holds σ) : StepOK σ (step ks t) := by
  unfold step
  split
  · trivial
  · exact h
  · rename_i f args
    split_ifs with h1 h2 h3 h4 h5
    · subst h1
      exact (holds_and σ args).mp h
    · subst h2
      obtain ⟨a, ha, hh⟩ := (holds_or σ args).mp h
      exact ⟨[a], List.mem_map.mpr ⟨a, ha, rfl⟩, by simp [hh]⟩
    · subst h3
      split
      · rename_i a b
        have := (holds_imp σ a b).mp h
        by_cases ha : a.Holds σ
        · exact ⟨[b], by simp, by simp [this ha]⟩
        · exact ⟨[neg a], by simp, by simp [holds_neg, ha]⟩
      · trivial
    · subst h4
      split
      · rename_i x
        exact stepNot_sound σ x ((holds_neg σ x).mp h)
      · trivial
    · split
      · rename_i a b
        exact atomStep_sound σ true f a b (by simpa [wrap] using h)
      · trivial
    · trivial
  · rename_i x body
    intro u hu
    simp only [instances, List.mem_filterMap] at hu
    obtain ⟨k, -, hk⟩ := hu
    split at hk
    · simp at hk
    · rename_i hb
      simp only [Option.some.injEq] at hk
      subst hk
      have hall : ∀ m : Int, body.Holds (σ.setI x m) := h
      have := hall (σ.i k)
      simp only [Tm.Holds] at this ⊢
      rw [Tm.eval_subst .int x (.ivar k) rfl body σ (fun y hy hyk => by
        simp only [Tm.vars, List.mem_cons, List.not_mem_nil, or_false] at hyk
        subst hyk; simp_all)]
      exact this
  · trivial

theorem resolve_eval (c : Tm) (b : Bool) (hc : if b then c.Holds σ else ¬ c.Holds σ) :
    ∀ (n : Nat) (t : Tm), (resolve c b n t).eval σ = t.eval σ
  | 0, _ => rfl
  | n + 1, t => by
    cases t with
    | app f args =>
      have hargs : (Tm.app f (args.map (resolve c b n))).eval σ = (Tm.app f args).eval σ := by
        rw [eval_app, eval_app, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact resolve_eval c b hc n a
      simp only [resolve]
      split
      · rename_i c' p q hi
        obtain ⟨h1, h2⟩ := isIte_sound σ hi
        split_ifs with hb hbb
        · have := Tm.eq_of_beq hb
          subst this
          rw [← hargs, h1 (by simpa [hbb] using hc)]
        · have := Tm.eq_of_beq hb
          subst this
          rw [← hargs, h2 (by simpa [hbb] using hc)]
        · exact hargs
      · exact hargs
    | _ => rfl

mutual
theorem Tm.mem_vars_of_binders : ∀ (t : Tm) {y : String}, y ∈ t.binders → y ∈ t.vars
  | .app _ args, y, h => by
    simp only [Tm.binders] at h
    simpa [Tm.vars] using Tm.mem_varsList_of_bindersList args h
  | .all x body, y, h => by
    simp only [Tm.binders, List.mem_cons] at h
    simp only [Tm.vars, List.mem_cons]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Tm.mem_vars_of_binders body h)
  | .num _, _, h | .tt, _, h | .ff, _, h | .ivar _, _, h | .bvar _, _, h | .avar _, _, h
  | .a2var _, _, h => by simp [Tm.binders] at h
theorem Tm.mem_varsList_of_bindersList : ∀ (ts : List Tm) {y : String}, y ∈ Tm.bindersList ts →
    y ∈ Tm.varsList ts
  | [], _, h => by simp [Tm.bindersList] at h
  | t :: ts, y, h => by
    simp only [Tm.bindersList, List.mem_append] at h
    simp only [Tm.varsList, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Tm.mem_vars_of_binders t h)
    · exact Or.inr (Tm.mem_varsList_of_bindersList ts h)
end

theorem agree_setI_ne {τ : Env} {x y : String} (m : Int) (h : y ≠ x) : (τ.setI x m).Agree τ y :=
  ⟨by simp [Env.setI, h], rfl, rfl, rfl⟩

theorem sumCs_congr {τ ρ : Env} (hu : τ.u = ρ.u) : ∀ (l : List (Tm × Int)), (∀ p ∈ l, ∀ y ∈ p.1.vars, τ.Agree ρ y) →
    sumCs τ l = sumCs ρ l
  | [], _ => rfl
  | p :: ps, h => by
    simp only [sumCs]
    rw [Tm.eval_congr p.1 hu (h p (by simp)), sumCs_congr hu ps (fun q hq => h q (by simp [hq]))]

/-! ### Definitions -/

theorem eqOf_sound {t v u : Tm} (h : eqOf? t = some (v, u)) (ht : t.Holds σ) :
    v.eval σ = u.eval σ := by
  unfold eqOf? at h
  split at h
  · rename_i f v' u'
    split_ifs at h with hc
    obtain ⟨rfl, hv⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [holds_app, List.map_cons, List.map_nil, applyOp, Value.toProp] at ht
    cases v' <;> simp [Tm.isConst] at hv <;> simp only [Tm.eval] at ht ⊢ <;>
      cases hu : u'.eval σ <;> simp [hu, Value.eq] at ht ⊢
    all_goals exact ht
  · simp at h

theorem lookupEq_mem : ∀ {eqs : List (Tm × Tm)} {v u : Tm}, lookupEq eqs v = some u →
    ∃ e ∈ eqs, e.1 = v ∧ e.2 = u
  | [], _, _, h => by simp [lookupEq] at h
  | e :: es, v, u, h => by
    simp only [lookupEq] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      exact ⟨e, by simp, Tm.eq_of_beq hb, h⟩
    · obtain ⟨e', he', h1, h2⟩ := lookupEq_mem h
      exact ⟨e', by simp [he'], h1, h2⟩

theorem substN_eval : ∀ (n : Nat) (eqs : List (Tm × Tm)) (σ : Env),
    (∀ e ∈ eqs, e.1.eval σ = e.2.eval σ) → ∀ t : Tm, (substN eqs n t).eval σ = t.eval σ
  | 0, _, _, _, _ => rfl
  | n + 1, eqs, σ, he, t => by
    cases t with
    | app f args =>
      simp only [substN, eval_app, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact substN_eval n eqs σ he a
    | all x body =>
      have hb : ∀ m : Int, (substN (eqs.filter fun e => !(e.1.vars.contains x || e.2.vars.contains x))
          n body).eval (σ.setI x m) = body.eval (σ.setI x m) := by
        intro m
        refine substN_eval n _ _ ?_ body
        intro e hm
        obtain ⟨hm, hx⟩ := List.mem_filter.mp hm
        have h1 : x ∉ e.1.vars := fun hm' => by simp [hm'] at hx
        have h2 : x ∉ e.2.vars := fun hm' => by simp [hm'] at hx
        rw [Tm.eval_congr e.1 (σ := σ.setI x m) (τ := σ) rfl
            (fun y hy => agree_setI_ne (x := x) m (fun h => h1 (h ▸ hy))),
          Tm.eval_congr e.2 (σ := σ.setI x m) (τ := σ) rfl
            (fun y hy => agree_setI_ne (x := x) m (fun h => h2 (h ▸ hy)))]
        exact he e hm
      simp only [substN, Tm.eval, hb]
    | _ =>
      simp only [substN]
      split_ifs
      · split
        · rename_i u hl
          obtain ⟨e, hm, h1, h2⟩ := lookupEq_mem hl
          rw [substN_eval n eqs σ he u, ← h2, ← he e hm, h1]
        · rfl
      · rfl

theorem iteEqs_sound (c : Tm) (hc : c.Holds σ) : ∀ e ∈ iteEqs c, e.1.eval σ = e.2.eval σ := by
  intro e he
  unfold iteEqs at he
  split at he
  · rename_i f a b
    by_cases h1 : f = "=" ∧ a.isIntAtom = true ∧ b.isIntAtom = true
    · rw [if_pos h1] at he
      obtain ⟨rfl, ha, hb⟩ := h1
      have ea := int_atom σ ha
      have eb := int_atom σ hb
      have hc' : (a.eval σ).toInt = (b.eval σ).toInt := by
        simp only [holds_app, List.map_cons, List.map_nil, applyOp, Value.toProp] at hc
        rw [ea, eb] at hc
        simpa [Value.eq] using hc
      have hab : a.eval σ = b.eval σ := by rw [ea, eb, hc']
      split at he
      · simp only [List.mem_singleton] at he; subst he; exact hab
      · split at he
        · simp only [List.mem_singleton] at he; subst he; exact hab.symm
        · simp at he
    · rw [if_neg h1] at he; simp at he
  · simp at he

/-- Setting a constant that occurs in none of the facts `ts` and constraints `cs` changes none of
their values. -/
theorem fresh_setI {x : String} {ts : List Tm} {cs : List Lin} (hf : fresh x ts cs = true) (m : Int) :
    (∀ t ∈ ts, t.eval (σ.setI x m) = t.eval σ) ∧ ∀ l ∈ cs, l.eval (σ.setI x m) = l.eval σ := by
  simp only [fresh, Bool.and_eq_true, List.all_eq_true] at hf
  refine ⟨fun t ht => Tm.eval_congr t (σ := σ.setI x m) (τ := σ) rfl fun y hy =>
      agree_setI_ne m fun e => ?_,
    fun l hl => congrArg (l.k + ·) (sumCs_congr (τ := σ.setI x m) (ρ := σ) rfl l.cs fun p hp y hy =>
      agree_setI_ne m fun e => ?_)⟩
  · subst e; have := hf.1 t ht; simp [hy] at this
  · subst e; have := hf.2 l hl p hp; simp [hy] at this

/-- The skolem step of `refute` and `refuteC`: whichever list of facts it continues with (`R`), some
assignment satisfies them and the constraints. -/
theorem skolem_sound {x : String} {u : Tm} {rest : List Tm} {cs : List Lin} (R : List Tm → Bool)
    (hR : ∀ τ ts, R ts = true → (∀ t ∈ ts, t.Holds τ) → (∀ l ∈ cs, l.eval τ ≤ 0) → False)
    (h : (if fresh x rest cs then R (u :: rest)
      else if fresh (x ++ "'") (u :: rest) cs then R (u.subst .int x (.ivar (x ++ "'")) :: rest)
      else R rest) = true)
    (hst : ∃ m : Int, u.Holds (σ.setI x m)) (hr : ∀ t ∈ rest, t.Holds σ)
    (hc : ∀ l ∈ cs, l.eval σ ≤ 0) : False := by
  obtain ⟨m, hm⟩ := hst
  split_ifs at h with hf hf'
  · have e := fresh_setI σ hf m
    refine hR _ _ h (List.forall_mem_cons.2 ⟨hm, fun t ht => ?_⟩) fun l hl => ?_
    · simpa only [Tm.Holds, e.1 t ht] using hr t ht
    · simpa only [e.2 l hl] using hc l hl
  · have e := fresh_setI σ hf' m
    have hx : x ++ "'" ∉ u.vars := fun hy => by
      simp only [fresh, Bool.and_eq_true, List.all_eq_true] at hf'
      have := hf'.1 u (by simp); simp [hy] at this
    refine hR (σ.setI (x ++ "'") m) _ h (List.forall_mem_cons.2 ⟨?_, fun t ht => ?_⟩) fun l hl => ?_
    · simp only [Tm.Holds] at hm ⊢
      rw [Tm.eval_subst .int x (.ivar (x ++ "'")) rfl u _ (fun y hy hyx => by
        simp only [Tm.vars, List.mem_cons, List.not_mem_nil, or_false] at hyx
        subst hyx
        exact hx (Tm.mem_vars_of_binders u hy)),
        show (Tm.ivar (x ++ "'")).eval (σ.setI (x ++ "'") m) = .int m by simp [Tm.eval, Env.setI]]
      rwa [Tm.eval_congr u (σ := (σ.setI (x ++ "'") m).set .int x (.int m)) (τ := σ.setI x m) rfl
        fun y hy => by
          have hy' : y ≠ x ++ "'" := fun e => hx (e ▸ hy)
          refine ⟨?_, rfl, rfl, rfl⟩
          simp only [Env.set, Env.setI, Value.toInt]
          by_cases hyx : y = x <;> simp [hyx, hy']]
    · simpa only [Tm.Holds, e.1 t (List.mem_cons_of_mem _ ht)] using hr t ht
    · simpa only [e.2 l hl] using hc l hl
  · exact hR _ _ h hr hc

/-- The two cases of an `ite` step, as `refute` and `refuteC` continue with them. -/
theorem ite_cases {c t1 t2 : Tm} {rest : List Tm} (hst : StepOK σ (.ite c t1 t2))
    (hr : ∀ u ∈ rest, u.Holds σ) :
    (c.Holds σ ∧ ∀ u ∈ c :: ((t1 :: rest).map (resolve c true resolveFuel)).map
      (substN (iteEqs c) substFuel), u.Holds σ) ∨
    ∀ u ∈ neg c :: (t2 :: rest).map (resolve c false resolveFuel), u.Holds σ := by
  rcases hst with ⟨hc1, ht1⟩ | ⟨hc2, ht2⟩
  · refine Or.inl ⟨hc1, List.forall_mem_cons.2 ⟨hc1, ?_⟩⟩
    simp only [List.forall_mem_map, Tm.Holds, substN_eval substFuel _ σ (iteEqs_sound σ c hc1),
      resolve_eval σ c true (by simpa using hc1)]
    exact List.forall_mem_cons.2 ⟨ht1, hr⟩
  · refine Or.inr (List.forall_mem_cons.2 ⟨(holds_neg σ c).2 hc2, ?_⟩)
    simp only [List.forall_mem_map, Tm.Holds, resolve_eval σ c false (by simpa using hc2)]
    exact List.forall_mem_cons.2 ⟨ht2, hr⟩

theorem refute_sound (F : Nat) (ks : List String) : ∀ (n b : Nat) (σ : Env) (ts : List Tm) (cs : List Lin),
    refute F ks n b ts cs = true → (∀ t ∈ ts, t.Holds σ) → (∀ l ∈ cs, l.eval σ ≤ 0) → False
  | 0, _, _, _, _, h, _, _ => by simp [refute] at h
  | n + 1, _, σ, [], cs, h, _, hc => fm_sound σ F cs (by simpa [refute] using h) hc
  | n + 1, b, σ, t :: rest, cs, h, ht, hc => by
    have hst := step_sound σ ks t (ht t (by simp))
    have hr : ∀ u ∈ rest, u.Holds σ := fun u hu => ht u (by simp [hu])
    simp only [refute] at h
    generalize step ks t = s at h hst
    cases s with
    | drop => exact refute_sound F ks n b σ rest cs h hr hc
    | closed => exact hst
    | facts us => exact refute_sound F ks n b σ _ cs h (List.forall_mem_append.2 ⟨hst, hr⟩) hc
    | cons ls => exact refute_sound F ks n b σ rest _ h hr (List.forall_mem_append.2 ⟨hst, hc⟩)
    | split bs =>
      rcases Bool.or_eq_true _ _ |>.mp h with h | h
      · exact fm_sound σ F cs h hc
      obtain ⟨us, hus, hall⟩ := hst
      exact refute_sound F ks n (b - 1) σ _ cs
        (List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).2 us hus)
        (List.forall_mem_append.2 ⟨hall, hr⟩) hc
    | ite c t1 t2 =>
      rcases Bool.or_eq_true _ _ |>.mp h with h | h
      · exact fm_sound σ F cs h hc
      simp only [Bool.and_eq_true] at h
      rcases ite_cases σ hst hr with ⟨-, h1⟩ | h2
      · exact refute_sound F ks n (b - 1) σ _ cs h.2.1 h1 hc
      · exact refute_sound F ks n (b - 1) σ _ cs h.2.2 h2 hc
    | skolem x u =>
      exact skolem_sound σ (refute F ks n b · cs) (fun τ ts h => refute_sound F ks n b τ ts cs h)
        h hst hr hc

open Classical in
/-- An `ite` of two values of one sort is the one its condition picks. -/
theorem applyOp_ite (u : String → List Int → Int) (c : Value) {X Y : Value} (h : X.sortOf = Y.sortOf) :
    applyOp u "ite" [c, X, Y] = if c.toProp then X else Y := by
  cases X <;> cases Y <;> simp_all [Value.sortOf, applyOp, apply_ite]

/-- Read over write, of an array of integers or a mapping of mappings. -/
theorem select_store {A V : Value}
    (h : (A.sortOf = .arr ∧ V.sortOf = .int) ∨ (A.sortOf = .arr2 ∧ V.sortOf = .arr)) (I J : Int) :
    (A.store I V).select J = if J = I then V else A.select J := by
  rcases h with ⟨ha, hv⟩ | ⟨ha, hv⟩ <;> cases A <;> cases V <;>
    simp_all [Value.sortOf, Value.store, Value.select, apply_ite, Value.toInt, Value.toArr]

theorem applyOp_select (u : String → List Int → Int) (a i : Value) :
    applyOp u "select" [a, i] = a.select i.toInt := by simp [applyOp]

theorem applyOp_store (u : String → List Int → Int) (a i v : Value) :
    applyOp u "store" [a, i, v] = a.store i.toInt v := by simp [applyOp]

theorem applyOp_eq (u : String → List Int → Int) (a b : Value) :
    applyOp u "=" [a, b] = .prop (a.eq b) := by simp [applyOp]

/-- Reads of two values of one sort have one sort. -/
theorem sortOf_select_congr {A B : Value} (h : A.sortOf = B.sortOf) (J K : Int) :
    (A.select J).sortOf = (B.select K).sortOf := by
  cases A <;> cases B <;> simp_all [Value.sortOf, Value.select]

theorem rowSel_eval {r : Tm → Tm} (hr : ∀ t, (r t).eval σ = t.eval σ) (x j : Tm) :
    (rowSel r x j).eval σ = (Tm.app "select" [x, j]).eval σ := by
  unfold rowSel
  split
  · rename_i g a i v
    by_cases h1 : g = "store" ∧ i.isIntAtom = true ∧ j.isIntAtom = true ∧ rowSorts a v = true
    · rw [if_pos h1]
      obtain ⟨rfl, hi, hj, hs⟩ := h1
      have hs' : ((a.eval σ).sortOf = .arr ∧ (v.eval σ).sortOf = .int) ∨
          ((a.eval σ).sortOf = .arr2 ∧ (v.eval σ).sortOf = .arr) := by
        simp only [rowSorts, Tm.isIntAtom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
        exact hs.imp (fun h => ⟨Tm.eval_sortOf a σ h.1, Tm.eval_sortOf v σ h.2⟩)
          (fun h => ⟨Tm.eval_sortOf a σ h.1, Tm.eval_sortOf v σ h.2⟩)
      obtain ⟨I, eI⟩ : ∃ I, i.eval σ = .int I := ⟨_, int_atom σ hi⟩
      obtain ⟨J, eJ⟩ : ∃ J, j.eval σ = .int J := ⟨_, int_atom σ hj⟩
      split_ifs with hb
      · obtain rfl := Tm.eq_of_beq hb
        simp [eval_app, applyOp, select_store hs', eJ, Value.toInt]
      · have hsort : (v.eval σ).sortOf = ((a.eval σ).select J).sortOf := by
          rcases hs' with ⟨ha, hv⟩ | ⟨ha, hv⟩ <;> revert ha <;> cases a.eval σ <;>
            simp_all [Value.sortOf, Value.select]
        simp only [eval_app, List.map, hr, applyOp_select, applyOp_store, applyOp_eq, eI, eJ, Value.toInt]
        rw [applyOp_ite _ _ hsort, select_store hs']
        simp only [Value.toProp, Value.eq]
        congr
    · rw [if_neg h1]
      by_cases h2 : g = "ite" ∧ arrPair i v = true
      · rw [if_pos h2]
        obtain ⟨rfl, hp⟩ := h2
        have hiv : (i.eval σ).sortOf = (v.eval σ).sortOf := by
          simp only [arrPair, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
          rcases hp with ⟨hi, hv⟩ | ⟨hi, hv⟩ <;> rw [Tm.eval_sortOf i σ hi, Tm.eval_sortOf v σ hv]
        simp only [eval_app, List.map, hr, applyOp_select]
        rw [applyOp_ite _ _ (sortOf_select_congr hiv _ _), applyOp_ite _ _ hiv]
        split <;> rfl
      · rw [if_neg h2]
  · rename_i g v
    by_cases hc : (g = isOpName.constName ∧ v.isIntAtom = true) ∨
        (g = isOpName.const2Name ∧ v.sort? = some .arr)
    · rw [if_pos hc]
      rcases hc with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
      · obtain ⟨V, eV⟩ : ∃ V, v.eval σ = .int V := ⟨_, int_atom σ hv⟩
        simp only [Tm.eval, Tm.evalList, isOpName.constName, applyOp, eV, Value.select, Value.toInt]
      · obtain ⟨eV', eV⟩ : ∃ X, v.eval σ = .arr X := ⟨_, Value.sortOf_arr (Tm.eval_sortOf v σ hv)⟩
        simp only [Tm.eval, Tm.evalList, isOpName.const2Name, applyOp, eV, Value.select, Value.toArr]
    · rw [if_neg hc]
  · rfl

theorem rowN_eval : ∀ (n : Nat) (σ : Env) (t : Tm), (rowN n t).eval σ = t.eval σ
  | 0, _, _ => rfl
  | n + 1, σ, t => by
    cases t with
    | all x body =>
      have hb : ∀ m : Int, (rowN n body).eval (σ.setI x m) = body.eval (σ.setI x m) :=
        fun m => rowN_eval n _ body
      simp only [rowN, Tm.eval, hb]
    | app f args =>
      have hargs : (args.map (rowN n)).map (Tm.eval σ) = args.map (Tm.eval σ) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a _
        exact rowN_eval n σ a
      simp only [rowN]
      split_ifs with hf
      · subst hf
        split
        · rename_i x j heq
          rw [rowSel_eval σ (rowN_eval n σ) x j]
          have hsel := congrArg (List.map (Tm.eval σ)) heq
          rw [hargs] at hsel
          rw [eval_app σ "select" [x, j], eval_app σ "select" args, hsel]
        · simp only [eval_app, hargs]
      · simp only [eval_app, hargs]
    | _ => rfl

theorem modFacts_holds {t : Tm} {m : Nat} (ht : t.isIntAtom = true) (hm : 0 < m) :
    ∀ u ∈ modFacts t m, u.Holds σ := by
  obtain ⟨T, eT⟩ : ∃ T, t.eval σ = .int T := ⟨_, int_atom σ ht⟩
  have hm' : (m : Int) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 := Int.mul_ediv_add_emod T m
  have h2 := Int.emod_nonneg T hm'
  have h3 := Int.emod_lt_of_pos T (by exact_mod_cast hm : (0 : Int) < m)
  have h4 : ((m - 1 : Nat) : Int) = m - 1 := by omega
  intro u hu
  simp only [modFacts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, eT, Value.toInt, Value.toProp, Value.eq, hm', h4]
  · omega
  · omega
  · omega
  · omega

theorem divFacts_holds (fs : List Tm) : ∀ u ∈ divFacts fs, u.Holds σ := by
  intro u hu
  simp only [divFacts, List.mem_flatMap] at hu
  obtain ⟨p, -, hu⟩ := hu
  split at hu
  · rename_i h
    exact modFacts_holds σ h.1 h.2 u hu
  · simp at hu

theorem mem_goalFirst {fs : List Tm} {t : Tm} (h : t ∈ goalFirst fs) : t ∈ fs := by
  simp only [goalFirst, List.mem_append] at h
  rcases h with h | h
  · exact List.mem_of_getLast? (by simpa using h)
  · exact List.dropLast_subset fs h

/-- The facts `refuteOb` reads, with or without the facts of `mod` and `div`, hold in every model of
the obligation. -/
theorem refuteOb_facts {fs : List Tm} (hσ : ∀ t ∈ fs, t.Holds σ) (d : Bool) :
    let rs := relevant ((fs.filter fun t => (eqOf? t).isNone).map
      fun t => rowN rowFuel (substN (fs.filterMap eqOf?) substFuel t))
    ∀ t ∈ (if d then goalFirst rs ++ divFacts rs else goalFirst rs), t.Holds σ := by
  intro rs
  have he : ∀ e ∈ fs.filterMap eqOf?, e.1.eval σ = e.2.eval σ := fun e hm => by
    obtain ⟨t, ht, hte⟩ := List.mem_filterMap.mp hm
    exact eqOf_sound σ hte (hσ t ht)
  have hg : ∀ t ∈ rs, t.Holds σ := fun t ht => by
    simp only [rs, relevant, List.mem_filter] at ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht.1
    simp only [Tm.Holds, rowN_eval _ σ, substN_eval _ _ σ he]
    exact hσ t' (List.mem_filter.mp ht').1
  cases d
  · exact fun t ht => hg t (mem_goalFirst ht)
  · exact List.forall_mem_append.2 ⟨fun t ht => hg t (mem_goalFirst ht), divFacts_holds σ _⟩

theorem refuteOb_sound {fs : List Tm} (h : refuteOb fs = true) : ∀ σ : Env, ¬ ∀ t ∈ fs, t.Holds σ := by
  intro σ hσ
  simp only [refuteOb, Bool.or_eq_true] at h
  rcases h with h | h
  · exact refute_sound fmFuel _ stepFuel splitFuel σ _ [] h (refuteOb_facts σ hσ false) (by simp)
  · exact refute_sound fmFuel _ stepFuel splitFuel σ _ [] h (refuteOb_facts σ hσ true) (by simp)

end Sound

/-- **The discharge is sound**: a script `dischargeScript` accepts is valid, every obligation of
it but the probes having no model. -/
theorem dischargeScript_sound (cs : List Cmd) (h : dischargeScript cs = true) : Valid cs := by
  intro fs hfs hp σ
  have := List.all_eq_true.mp h fs hfs
  simp only [hp, Bool.false_or] at this
  exact refuteOb_sound this σ

/-- **The discharge, one obligation at a time.** -/
theorem dischargeScript_of_each (cs : List Cmd)
    (h : ∀ i < (obligations cs).length, dischargeAt cs i = true) : Valid cs := by
  intro fs hfs hp σ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfs
  have := h i hi
  simp only [dischargeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some, hp, Bool.false_or] at this
  exact refuteOb_sound this σ

/-- An obligation the discharge rejects makes it reject the script. -/
theorem dischargeScript_false_of {cs : List Cmd} {i : Nat} (hi : i < (obligations cs).length)
    (h : dischargeAt cs i = false) : dischargeScript cs = false := by
  simp only [dischargeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some] at h
  simp only [dischargeScript, List.all_eq_false]
  exact ⟨_, List.getElem_mem hi, by simp [h]⟩

/-- Whether the obligation at index `i` is vacuous: its hypotheses, without the negated goal, already
have no model, so it holds only because the path it covers is unreachable. A report, never a
verdict: `false` means only that the discharge found no contradiction among the hypotheses. -/
def vacuousAt (cs : List Cmd) (i : Nat) : Bool :=
  refuteOb ((obligations cs).getD i []).dropLast

/-- A vacuous obligation's hypotheses have no model. -/
theorem vacuousAt_sound {cs : List Cmd} {i : Nat} (h : vacuousAt cs i = true) :
    ∀ σ : Env, ¬ ∀ t ∈ ((obligations cs).getD i []).dropLast, t.Holds σ :=
  refuteOb_sound h

end SolidCore.Verify.VC

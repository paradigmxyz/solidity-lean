/-!
# SMT-LIB terms of solar-verify's verification conditions

solar-verify proves a function by sending SMT-LIB to a solver: constants with their sorts, the
facts it assumes, and for each obligation a `check-sat` of the guard of the paths that return
normally and the negation of what they must show. `Tm` is the fragment of SMT-LIB terms it emits
over integers, booleans and arrays from integers to integers, and `Cmd` its commands. Every
constant carries its sort (`Tm.ivar`, `Tm.bvar`, `Tm.avar`), as its `declare-const` gives it,
so an assignment of the constants (`Env`) is well sorted by construction.

`Tm.eval` is the meaning SMT-LIB gives the theory of integers with arrays, with one model of what
SMT-LIB leaves open: `div` and `mod` by zero are 0. An obligation that holds in every model holds in
this one. A term the fragment does not cover (a wrong arity or sort) means the default value of its
sort: the checks of `Check` compare terms by their syntax, so such a term can
only make a check fail.

`Tm.print` prints a term as solar-verify does, so that a script's print can be compared with the
bytes solar-verify sent the solver.
-/

namespace SolidCore.Verify.VC

/-- The sorts of the fragment. -/
inductive Srt where
  | int | bool | arr
  /-- `(Array Int (Array Int Int))`. -/
  | arr2
  deriving DecidableEq, Repr

/-- A term. Numerals are naturals; a negative integer is `(- n)`. -/
inductive Tm where
  | num (n : Nat)
  | tt
  | ff
  | ivar (x : String)
  | bvar (x : String)
  | avar (x : String)
  /-- A constant of sort `(Array Int (Array Int Int))`. -/
  | a2var (x : String)
  | app (f : String) (args : List Tm)
  /-- `(forall ((x Int)) body)`. -/
  | all (x : String) (body : Tm)
  deriving Repr, Inhabited

/-! ## Equality of terms, by structural recursion (the kernel evaluates it) -/

mutual
def Tm.beq : Tm → Tm → Bool
  | .num a, .num b => a == b
  | .tt, .tt => true
  | .ff, .ff => true
  | .ivar a, .ivar b => a == b
  | .bvar a, .bvar b => a == b
  | .avar a, .avar b => a == b
  | .a2var a, .a2var b => a == b
  | .app f as, .app g bs => f == g && Tm.beqList as bs
  | .all x a, .all y b => x == y && Tm.beq a b
  | _, _ => false
def Tm.beqList : List Tm → List Tm → Bool
  | [], [] => true
  | a :: as, b :: bs => Tm.beq a b && Tm.beqList as bs
  | _, _ => false
end

mutual
theorem Tm.eq_of_beq : ∀ {a b : Tm}, Tm.beq a b = true → a = b
  | .num a, .num b, h => by simp [Tm.beq] at h; rw [h]
  | .tt, .tt, _ => rfl
  | .ff, .ff, _ => rfl
  | .ivar a, .ivar b, h => by simp [Tm.beq] at h; rw [h]
  | .bvar a, .bvar b, h => by simp [Tm.beq] at h; rw [h]
  | .avar a, .avar b, h => by simp [Tm.beq] at h; rw [h]
  | .a2var a, .a2var b, h => by simp [Tm.beq] at h; rw [h]
  | .app f as, .app g bs, h => by
    simp only [Tm.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Tm.eq_of_beqList h.2]
  | .all x a, .all y b, h => by
    simp only [Tm.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Tm.eq_of_beq h.2]
  | .num _, .tt, h | .num _, .ff, h | .num _, .ivar _, h | .num _, .bvar _, h | .num _, .avar _, h | .num _, .a2var _, h | .num _, .app _ _, h | .num _, .all _ _, h => by simp [Tm.beq] at h
  | .tt, .num _, h | .tt, .ff, h | .tt, .ivar _, h | .tt, .bvar _, h | .tt, .avar _, h | .tt, .a2var _, h | .tt, .app _ _, h | .tt, .all _ _, h => by simp [Tm.beq] at h
  | .ff, .num _, h | .ff, .tt, h | .ff, .ivar _, h | .ff, .bvar _, h | .ff, .avar _, h | .ff, .a2var _, h | .ff, .app _ _, h | .ff, .all _ _, h => by simp [Tm.beq] at h
  | .ivar _, .num _, h | .ivar _, .tt, h | .ivar _, .ff, h | .ivar _, .bvar _, h | .ivar _, .avar _, h | .ivar _, .a2var _, h | .ivar _, .app _ _, h | .ivar _, .all _ _, h => by simp [Tm.beq] at h
  | .bvar _, .num _, h | .bvar _, .tt, h | .bvar _, .ff, h | .bvar _, .ivar _, h | .bvar _, .avar _, h | .bvar _, .a2var _, h | .bvar _, .app _ _, h | .bvar _, .all _ _, h => by simp [Tm.beq] at h
  | .avar _, .num _, h | .avar _, .tt, h | .avar _, .ff, h | .avar _, .ivar _, h | .avar _, .bvar _, h | .avar _, .a2var _, h | .avar _, .app _ _, h | .avar _, .all _ _, h => by simp [Tm.beq] at h
  | .a2var _, .num _, h | .a2var _, .tt, h | .a2var _, .ff, h | .a2var _, .ivar _, h | .a2var _, .bvar _, h | .a2var _, .avar _, h | .a2var _, .app _ _, h | .a2var _, .all _ _, h => by simp [Tm.beq] at h
  | .app _ _, .num _, h | .app _ _, .tt, h | .app _ _, .ff, h | .app _ _, .ivar _, h | .app _ _, .bvar _, h | .app _ _, .avar _, h | .app _ _, .a2var _, h | .app _ _, .all _ _, h => by simp [Tm.beq] at h
  | .all _ _, .num _, h | .all _ _, .tt, h | .all _ _, .ff, h | .all _ _, .ivar _, h | .all _ _, .bvar _, h | .all _ _, .avar _, h | .all _ _, .a2var _, h | .all _ _, .app _ _, h => by simp [Tm.beq] at h
theorem Tm.eq_of_beqList : ∀ {as bs : List Tm}, Tm.beqList as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Tm.beqList, Bool.and_eq_true] at h
    rw [Tm.eq_of_beq h.1, Tm.eq_of_beqList h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Tm.beqList] at h
end

instance : BEq Tm := ⟨Tm.beq⟩

/-! ## Values and assignments -/

/-- A value of one of the sorts. A boolean is a proposition: a quantifier's value need not be
decidable. -/
inductive Value where
  | int (n : Int)
  | prop (p : Prop)
  | arr (f : Int → Int)
  | arr2 (f : Int → Int → Int)

def Value.toInt : Value → Int
  | .int n => n
  | _ => 0

def Value.toProp : Value → Prop
  | .prop p => p
  | _ => False

def Value.toArr : Value → (Int → Int)
  | .arr f => f
  | _ => fun _ => 0

def Value.toArr2 : Value → (Int → Int → Int)
  | .arr2 f => f
  | _ => fun _ _ => 0

/-- `(select a i)`: an integer of an array, or an array of a mapping of mappings. -/
def Value.select : Value → Int → Value
  | .arr2 f, i => .arr (f i)
  | .arr f, i => .int (f i)
  | .int _, _ => .int 0
  | .prop _, _ => .int 0

/-- `(store a i v)`. -/
def Value.store : Value → Int → Value → Value
  | .arr2 f, i, v => .arr2 (fun j => if j = i then v.toArr else f j)
  | .arr f, i, v => .arr (fun j => if j = i then v.toInt else f j)
  | .int _, i, v => .arr (fun j => if j = i then v.toInt else 0)
  | .prop _, i, v => .arr (fun j => if j = i then v.toInt else 0)

/-- The integer a `select` reads is the array's entry, for every value: a mapping of mappings and a
non-array read as 0 on both sides. -/
theorem Value.toInt_select (v : Value) (i : Int) : (v.select i).toInt = v.toArr i := by
  cases v <;> rfl

/-- Whether a value has a sort. -/
def Value.Sorted : Value → Srt → Prop
  | .int _, .int => True
  | .prop _, .bool => True
  | .arr _, .arr => True
  | .arr2 _, .arr2 => True
  | _, _ => False

/-- An assignment of the constants and bound variables, one function per sort, and of the
uninterpreted functions (`u`), from the integers of their arguments. -/
structure Env where
  i : String → Int
  b : String → Prop
  a : String → (Int → Int)
  a2 : String → (Int → Int → Int) := fun _ _ _ => 0
  u : String → List Int → Int := fun _ _ => 0

def Env.setI (σ : Env) (x : String) (n : Int) : Env :=
  { σ with i := fun y => if y = x then n else σ.i y }
def Env.setB (σ : Env) (x : String) (p : Prop) : Env :=
  { σ with b := fun y => if y = x then p else σ.b y }
def Env.setA (σ : Env) (x : String) (f : Int → Int) : Env :=
  { σ with a := fun y => if y = x then f else σ.a y }
def Env.setA2 (σ : Env) (x : String) (f : Int → Int → Int) : Env :=
  { σ with a2 := fun y => if y = x then f else σ.a2 y }

open Classical in
/-- Equality of two values of one sort. -/
noncomputable def Value.eq : Value → Value → Prop
  | .int a, .int b => a = b
  | .prop a, .prop b => (a ↔ b)
  | .arr a, .arr b => a = b
  | .arr2 a, .arr2 b => a = b
  | _, _ => False

/-- The operators of the fragment; every other name applied is an uninterpreted function. -/
def isOpName (f : String) : Bool :=
  f == "+" || f == "-" || f == "*" || f == "div" || f == "mod" || f == "<=" || f == "<" ||
  f == ">=" || f == ">" || f == "=" || f == "not" || f == "=>" || f == "and" || f == "or" ||
  f == "ite" || f == "select" || f == "store" || f == constName || f == const2Name
where
  constName := "(as const (Array Int Int))"
  const2Name := "(as const (Array Int (Array Int Int)))"

open Classical in
/-- The meaning of an operator applied to the values of its arguments; `u` interprets the
uninterpreted functions. -/
noncomputable def applyOp (u : String → List Int → Int) : String → List Value → Value
  | "+", [a, b] => .int (a.toInt + b.toInt)
  | "+", as => .int (as.map Value.toInt).sum
  | "-", [a] => .int (-a.toInt)
  | "-", [a, b] => .int (a.toInt - b.toInt)
  | "*", [a, b] => .int (a.toInt * b.toInt)
  | "div", [a, b] => .int (if b.toInt = 0 then 0 else a.toInt / b.toInt)
  | "mod", [a, b] => .int (if b.toInt = 0 then 0 else a.toInt % b.toInt)
  | "<=", [a, b] => .prop (a.toInt ≤ b.toInt)
  | "<", [a, b] => .prop (a.toInt < b.toInt)
  | ">=", [a, b] => .prop (a.toInt ≥ b.toInt)
  | ">", [a, b] => .prop (a.toInt > b.toInt)
  | "=", [a, b] => .prop (a.eq b)
  | "not", [a] => .prop (¬ a.toProp)
  | "=>", [a, b] => .prop (a.toProp → b.toProp)
  | "and", as => .prop (∀ v ∈ as, v.toProp)
  | "or", as => .prop (∃ v ∈ as, v.toProp)
  | "ite", [c, .int a, .int b] => .int (if c.toProp then a else b)
  | "ite", [c, .prop a, .prop b] => .prop (if c.toProp then a else b)
  | "ite", [c, .arr a, .arr b] => .arr (if c.toProp then a else b)
  | "ite", [c, .arr2 a, .arr2 b] => .arr2 (if c.toProp then a else b)
  | "select", [a, i] => a.select i.toInt
  | "store", [a, i, v] => a.store i.toInt v
  | "(as const (Array Int Int))", [v] => .arr (fun _ => v.toInt)
  | "(as const (Array Int (Array Int Int)))", [v] => .arr2 (fun _ => v.toArr)
  | f, vs => .int (if isOpName f then 0 else u f (vs.map Value.toInt))

mutual
noncomputable def Tm.eval (σ : Env) : Tm → Value
  | .num n => .int n
  | .tt => .prop True
  | .ff => .prop False
  | .ivar x => .int (σ.i x)
  | .bvar x => .prop (σ.b x)
  | .avar x => .arr (σ.a x)
  | .a2var x => .arr2 (σ.a2 x)
  | .app f args => applyOp σ.u f (Tm.evalList σ args)
  | .all x body => .prop (∀ n : Int, (Tm.eval (σ.setI x n) body).toProp)
noncomputable def Tm.evalList (σ : Env) : List Tm → List Value
  | [] => []
  | t :: ts => Tm.eval σ t :: Tm.evalList σ ts
end

theorem Tm.evalList_eq (σ : Env) : ∀ ts : List Tm, Tm.evalList σ ts = ts.map (Tm.eval σ)
  | [] => rfl
  | t :: ts => by rw [Tm.evalList, Tm.evalList_eq σ ts]; rfl

/-- A term holds. -/
def Tm.Holds (σ : Env) (t : Tm) : Prop := (t.eval σ).toProp

/-! ## Sorts of terms -/

/-- The sort of a term, when the fragment gives it one. -/
def sortOp : String → List (Option Srt) → Option Srt
  | "+", [some .int, some .int] => some .int
  | "-", [some .int] => some .int
  | "-", [some .int, some .int] => some .int
  | "*", [some .int, some .int] => some .int
  | "div", [some .int, some .int] => some .int
  | "mod", [some .int, some .int] => some .int
  | "<=", [some .int, some .int] => some .bool
  | "<", [some .int, some .int] => some .bool
  | ">=", [some .int, some .int] => some .bool
  | ">", [some .int, some .int] => some .bool
  | "=", [some a, some b] => if a = b then some .bool else none
  | "not", [some .bool] => some .bool
  | "=>", [some .bool, some .bool] => some .bool
  | "and", ss => if ss.all (· == some .bool) then some .bool else none
  | "or", ss => if ss.all (· == some .bool) then some .bool else none
  | "ite", [some .bool, some a, some b] => if a = b then some a else none
  | "select", [some .arr, some .int] => some .int
  | "store", [some .arr, some .int, some .int] => some .arr
  | "select", [some .arr2, some .int] => some .arr
  | "store", [some .arr2, some .int, some .arr] => some .arr2
  | "(as const (Array Int Int))", [some .int] => some .arr
  | "(as const (Array Int (Array Int Int)))", [some .arr] => some .arr2
  | f, ss => if isOpName f = false ∧ ss ≠ [] then some .int else none

mutual
def Tm.sort? : Tm → Option Srt
  | .num _ => some .int
  | .tt => some .bool
  | .ff => some .bool
  | .ivar _ => some .int
  | .bvar _ => some .bool
  | .avar _ => some .arr
  | .a2var _ => some .arr2
  | .app f args => sortOp f (Tm.sortList args)
  | .all _ body => if Tm.sort? body = some .bool then some .bool else none
def Tm.sortList : List Tm → List (Option Srt)
  | [] => []
  | t :: ts => Tm.sort? t :: Tm.sortList ts
end

/-! ## Printing, as solar-verify prints SMT-LIB -/

mutual
def Tm.print : Tm → String
  | .num n => toString n
  | .tt => "true"
  | .ff => "false"
  | .ivar x => "|" ++ x ++ "|"
  | .bvar x => "|" ++ x ++ "|"
  | .avar x => "|" ++ x ++ "|"
  | .a2var x => "|" ++ x ++ "|"
  | .app f args => "(" ++ f ++ Tm.printArgs args ++ ")"
  | .all x body => "(forall ((|" ++ x ++ "| Int)" ++ Tm.printBody body
def Tm.printArgs : List Tm → String
  | [] => ""
  | t :: ts => " " ++ Tm.print t ++ Tm.printArgs ts
/-- The rest of a quantifier's print: directly nested quantifiers print as one with several
binders, as solar-verify writes `(forall ((x Int) (y Int)) body)`. -/
def Tm.printBody : Tm → String
  | .all y body => " (|" ++ y ++ "| Int)" ++ Tm.printBody body
  | .app f args => ") (" ++ f ++ Tm.printArgs args ++ "))"
  | t => ") " ++ Tm.printLeaf t ++ ")"
/-- A term without subterms. -/
def Tm.printLeaf : Tm → String
  | .num n => toString n
  | .tt => "true"
  | .ff => "false"
  | .ivar x | .bvar x | .avar x | .a2var x => "|" ++ x ++ "|"
  | _ => ""
end

def Srt.print : Srt → String
  | .int => "Int"
  | .bool => "Bool"
  | .arr => "(Array Int Int)"
  | .arr2 => "(Array Int (Array Int Int))"

/-! ## Scripts -/

/-- A command of a script. `raw` is a line the checks do not read (a comment, `(push 1)` around a
function); `elem x lo hi` is solar-verify's `;@elem` hint that the elements of the array `x` lie
in `[lo, hi]`, which the checks do not take as a fact. -/
inductive Cmd where
  | decl (x : String) (s : Srt)
  | assert (t : Tm)
  | push
  | pop
  | checkSat
  | elem (x : String) (lo hi : Nat)
  /-- `(declare-fun f (Int … Int) Int)`, with `n` arguments. -/
  | declFun (f : String) (n : Nat)
  | raw (line : String)
  deriving Repr, Inhabited

def Cmd.print : Cmd → String
  | .decl x s => "(declare-const |" ++ x ++ "| " ++ s.print ++ ")"
  | .assert t => "(assert " ++ t.print ++ ")"
  | .push => "(push 1)"
  | .pop => "(pop 1)"
  | .checkSat => "(check-sat)"
  | .elem x lo hi => ";@elem |" ++ x ++ "| " ++ toString lo ++ " " ++ toString hi
  | .declFun f n => "(declare-fun " ++ f ++ " (" ++ " ".intercalate (List.replicate n "Int") ++ ") Int)"
  | .raw l => l

/-- A script's print: one command per line, each line ending in a newline. -/
def printScript (cs : List Cmd) : String :=
  String.join (cs.map fun c => c.print ++ "\n")

/-! ## Obligations

At each `check-sat` the solver is asked whether the facts asserted so far, in every open `push`,
have a model. solar-verify asks it of the obligations it owes, which hold when there is none, and
of one probe per function, `(assert (not false))` after the guard, which asks whether some path
returns at all and owes nothing. -/

/-- The facts asserted when the commands `cs` have run from the stack `stk` (innermost frame
first), and at each `check-sat` the facts it reads, in order. -/
def obligationsFrom : List (List Tm) → List Cmd → List (List Tm)
  | _, [] => []
  | stk, .assert t :: cs =>
    match stk with
    | [] => obligationsFrom [[t]] cs
    | f :: rest => obligationsFrom ((t :: f) :: rest) cs
  | stk, .push :: cs => obligationsFrom ([] :: stk) cs
  | stk, .pop :: cs => obligationsFrom (stk.drop 1) cs
  | stk, .checkSat :: cs => stk.flatten.reverse :: obligationsFrom stk cs
  | stk, _ :: cs => obligationsFrom stk cs

/-- The facts each `check-sat` of a script reads, oldest first. -/
def obligations (cs : List Cmd) : List (List Tm) := obligationsFrom [[]] cs

/-- A `check-sat` that only probes whether a path returns: its last fact is `(not false)`. -/
def isProbe (fs : List Tm) : Bool :=
  match fs.getLast? with
  | some (.app "not" [.ff]) => true
  | _ => false

/-- What solar-verify's verdict claims of a script: every obligation's facts have no model. -/
def Valid (cs : List Cmd) : Prop :=
  ∀ fs ∈ obligations cs, isProbe fs = false → ∀ σ : Env, ¬ ∀ t ∈ fs, t.Holds σ

end SolidCore.Verify.VC

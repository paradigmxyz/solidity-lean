import SolidCore.Spec.Syntax

/-!
# solar-verify's spec language: meaning

The meaning of a spec over a call and what it observes (`SolarTV.Call`, `SolarTV.Observable`),
the interface SolidCore, solar's IRs and EthLib share, so that the same predicate holds of the
source and of the bytecode a refinement relates it to.

* `eval`: a spec expression's value, an `Int`, from the call's arguments and return values, the
  pre- and post-state (storage, ghost state, `__time`) and the call's environment. Arithmetic is
  on mathematical integers; division and remainder truncate toward zero; `&`, `|`, `^` work on the
  256-bit two's complement words of their operands; `<<` by a literal wraps modulo `2 ^ 256`. These
  are solar-verify's own spec encodings (`src/vc.rs`, `arith` in spec mode). Where solar-verify
  leaves a value unconstrained (division by zero, a negative exponent), any value here is sound
  for its proofs, and this one picks Lean's.
* Quantifiers range over the binder's type, as solar-verify's `quant` does. They make `eval`
  noncomputable: a formula's meaning is a proposition.
* A spec function call evaluates the function's body with its parameters bound to the
  arguments' values. Calls nest at most `fuel` deep: `Term.Closed` checks that the exported fuel
  suffices, so the out-of-fuel case (`0`) is never reached in an exported spec. An opaque
  function means its body too; solar-verify proves facts about it for every interpretation in its
  return type's range, which includes this one exactly when `OpaqueInRange` holds.
* `Pre` and `Post` state a function's spec: the call selects the function and its arguments
  decode (ABI-clean words of their types), and from a pre-state meeting the requires and the
  contract invariants, a successful call returns clean words meeting the ensures and leaves a
  state meeting the invariants, and one meeting the succeeds-if conditions succeeds.
* `Holds S p scope cs ctxOf step`: every function's spec holds of program `p` in semantics `S` on
  `scope`, with ghost state updated by `step`. A ghost-free spec does not depend on `step`
  (`Holds.ghostFree`).
-/

namespace SolidCore.Spec

open SolarTV

/-- Storage: slot to word. -/
abbrev Storage := Nat → Nat

/-- Ghost state: each ghost variable, as a function of its mapping keys (none for a scalar). -/
abbrev Ghost := String → List Int → Int

/-- The ghost state at deployment: every ghost zero. -/
def Ghost.zero : Ghost := fun _ _ => 0

/-- `2 ^ 256`. -/
abbrev wordMod : Nat := 2 ^ 256

/-- The 256-bit word of an integer (two's complement for negative ones). -/
def toWord (v : Int) : Nat := (v % (wordMod : Int)).toNat

/-- The 32 big-endian bytes of a word. -/
def wordBytes (v : Nat) : List Nat := (List.range 32).reverse.map fun i => v / 256 ^ i % 256

/-- The big-endian word of a byte list. -/
def bytesWord (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-- Keccak-256 of a byte list, as a word: the definition SolidCore and EthLib both use. -/
def keccakWord (bs : List Nat) : Nat := bytesWord (EvmYul.SpongeHash.Keccak256.keccak256Bytes bs)

/-! ## Types -/

/-- The values of a type. -/
def Ty.InRange : Ty → Int → Prop
  | .uint b, v => 0 ≤ v ∧ v < 2 ^ b
  | .int b, v => -(2 ^ (b - 1)) ≤ v ∧ v < 2 ^ (b - 1)
  | .bool, v => v = 0 ∨ v = 1
  | .address, v => 0 ≤ v ∧ v < 2 ^ 160
  | .fixedBytes n, v => 0 ≤ v ∧ v < 2 ^ (8 * n)
  | .enum c, v => 0 ≤ v ∧ v < c
  | .math, _ => True

instance (t : Ty) (v : Int) : Decidable (t.InRange v) := by
  cases t <;> unfold Ty.InRange <;> infer_instance

/-- A value of type `t` from the `8 * bits` low bits of a storage word, as Solidity reads it. -/
def Ty.ofBits : Ty → Nat → Int
  | .int b, raw => if 2 ^ (b - 1) ≤ raw then (raw : Int) - 2 ^ b else raw
  | .bool, raw => if raw = 0 then 0 else 1
  | _, raw => raw

/-- A value of type `t` from an ABI word, or `none` when the word is not clean for `t` (Solidity's
decoder reverts on it). `bytesN` is left-aligned. -/
def Ty.ofWord : Ty → Nat → Option Int
  | .uint b, w => if w < 2 ^ b then some w else none
  | .int b, w =>
    if w < 2 ^ (b - 1) then some w
    else if wordMod - 2 ^ (b - 1) ≤ w ∧ w < wordMod then some ((w : Int) - wordMod)
    else none
  | .bool, w => if w ≤ 1 then some w else none
  | .address, w => if w < 2 ^ 160 then some w else none
  | .fixedBytes n, w =>
    if w < wordMod ∧ w % 2 ^ (8 * (32 - n)) = 0 then some (w / 2 ^ (8 * (32 - n)) : Nat) else none
  | .enum c, w => if w < c then some w else none
  | .math, _ => none

/-! ## States and environments -/

/-- What a spec reads of a state: storage, ghost state and `__time`. -/
structure State where
  storage : Storage
  ghost : Ghost
  time : Int

/-- The call's environment. -/
structure Ctx where
  sender : Int
  value : Int
  timestamp : Int
  self : Int

/-- Everything a spec expression reads. `inOld` is set inside `old(..)`. -/
structure Env where
  args : List Int
  rets : List Int
  pre : State
  post : State
  ctx : Ctx
  vars : List (String × Int)
  inOld : Bool

/-- The state a read sees. -/
def Env.cur (e : Env) : State := if e.inOld then e.pre else e.post

/-- Bind a variable. -/
def Env.bind (e : Env) (x : String) (v : Int) : Env := { e with vars := (x, v) :: e.vars }

/-- A truth value as `0` or `1`. -/
noncomputable def ofProp (p : Prop) : Int := by
  classical exact if p then 1 else 0

/-- Binary operators on values. -/
noncomputable def BinOp.apply : BinOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a.tdiv b
  | .mod, a, b => a.tmod b
  | .pow, a, b => a ^ b.toNat
  | .band, a, b => (toWord a &&& toWord b : Nat)
  | .bor, a, b => (toWord a ||| toWord b : Nat)
  | .bxor, a, b => (toWord a ^^^ toWord b : Nat)
  | .eq, a, b => ofProp (a = b)
  | .ne, a, b => ofProp (a ≠ b)
  | .lt, a, b => ofProp (a < b)
  | .le, a, b => ofProp (a ≤ b)
  | .gt, a, b => ofProp (a > b)
  | .ge, a, b => ofProp (a ≥ b)
  | .and, a, b => ofProp (a ≠ 0 ∧ b ≠ 0)
  | .or, a, b => ofProp (a ≠ 0 ∨ b ≠ 0)
  | .implies, a, b => ofProp (a ≠ 0 → b ≠ 0)

/-! ## Evaluation -/

mutual
/-- The value of a spec expression, with spec function calls nested at most `fuel` deep. -/
noncomputable def eval (fns : List SpecFn) (fuel : Nat) : Term → Env → Int
  | .lit v, _ => v
  | .arg i, e => e.args.getD i 0
  | .ret i, e => e.rets.getD i 0
  | .var x, e => (e.vars.lookup x).getD 0
  | .env .sender, e => e.ctx.sender
  | .env .value, e => e.ctx.value
  | .env .timestamp, e => e.ctx.timestamp
  | .env .self, e => e.ctx.self
  | .env .time, e => e.cur.time
  | .load p off size ty, e =>
    ty.ofBits (e.cur.storage (slotOf fns fuel p e) / 2 ^ (8 * toWord (eval fns fuel off e)) %
      2 ^ (8 * size))
  | .len p, e => e.cur.storage (slotOf fns fuel p e)
  | .ghost x ks, e => e.cur.ghost x (evalList fns fuel ks e)
  | .old t, e => eval fns fuel t { e with inOld := true }
  | .un .neg t, e => -eval fns fuel t e
  | .un .not t, e => ofProp (eval fns fuel t e = 0)
  | .bin op a b, e => op.apply (eval fns fuel a e) (eval fns fuel b e)
  | .shl t k, e => (eval fns fuel t e * 2 ^ k) % (wordMod : Int)
  | .shr t k, e => eval fns fuel t e / 2 ^ k
  | .ite c a b, e => if eval fns fuel c e ≠ 0 then eval fns fuel a e else eval fns fuel b e
  | .all x ty body, e => ofProp (∀ v, ty.InRange v → eval fns fuel body (e.bind x v) ≠ 0)
  | .ex x ty body, e => ofProp (∃ v, ty.InRange v ∧ eval fns fuel body (e.bind x v) ≠ 0)
  | .call f args, e =>
    match fuel, fns.find? (·.name == f) with
    | fuel' + 1, some sf =>
      eval fns fuel' sf.body { e with vars := (sf.params.map Prod.fst).zip (evalList fns (fuel' + 1) args e) }
    | _, _ => 0
termination_by t => (fuel, sizeOf t)

/-- The values of a list of spec expressions. -/
noncomputable def evalList (fns : List SpecFn) (fuel : Nat) : List Term → Env → List Int
  | [], _ => []
  | t :: ts, e => eval fns fuel t e :: evalList fns fuel ts e
termination_by ts => (fuel, sizeOf ts)

/-- The slot of a place. -/
noncomputable def slotOf (fns : List SpecFn) (fuel : Nat) : Place → Env → Nat
  | .slot n, _ => n % wordMod
  | .offset b k, e => (slotOf fns fuel b e + toWord (eval fns fuel k e)) % wordMod
  | .entry b k, e => keccakWord (wordBytes (toWord (eval fns fuel k e)) ++ wordBytes (slotOf fns fuel b e))
  | .elem b i n, e =>
    (keccakWord (wordBytes (slotOf fns fuel b e)) + toWord (eval fns fuel i e) * n) % wordMod
  | .packedElem b i n, e =>
    (keccakWord (wordBytes (slotOf fns fuel b e)) + toWord (eval fns fuel i e) / n) % wordMod
termination_by p => (fuel, sizeOf p)
end

/-- A formula holds: its value is nonzero. -/
def Holds' (fns : List SpecFn) (fuel : Nat) (t : Term) (e : Env) : Prop := eval fns fuel t e ≠ 0


/-! ## Evaluation lemmas -/

@[simp] theorem ofProp_ne_zero (p : Prop) : ofProp p ≠ 0 ↔ p := by
  unfold ofProp; split <;> simp_all

@[simp] theorem ofProp_eq_zero (p : Prop) : ofProp p = 0 ↔ ¬p := by
  unfold ofProp; split <;> simp_all

@[simp] theorem toWord_natCast {n : Nat} (h : n < 2 ^ 256) : toWord (n : Int) = n := by
  have h' : (n : Int) < ((wordMod : Nat) : Int) := by exact_mod_cast h
  unfold toWord
  rw [Int.emod_eq_of_lt (by omega) h']
  simp

/-! ## Well-formedness, checked by the kernel on every exported spec -/

mutual
/-- One level of `Term.Closed`: every call in `t` names a function of `fns` with as many arguments
as it has parameters, and `k` holds of the body it unfolds. Structural, so the kernel evaluates it. -/
def Term.closedWith (fns : List SpecFn) (k : Term → Bool) : Term → Bool
  | .load p off _ _ => Place.closedWith fns k p && Term.closedWith fns k off
  | .len p => Place.closedWith fns k p
  | .ghost _ ks => Term.closedListWith fns k ks
  | .old t | .un _ t | .shl t _ | .shr t _ | .all _ _ t | .ex _ _ t => Term.closedWith fns k t
  | .bin _ a b => Term.closedWith fns k a && Term.closedWith fns k b
  | .ite c a b => Term.closedWith fns k c && Term.closedWith fns k a && Term.closedWith fns k b
  | .call f args =>
    Term.closedListWith fns k args &&
    match fns.find? (·.name == f) with
    | some sf => sf.params.length == args.length && k sf.body
    | none => false
  | .lit _ | .arg _ | .ret _ | .var _ | .env _ => true

def Term.closedListWith (fns : List SpecFn) (k : Term → Bool) : List Term → Bool
  | [] => true
  | t :: ts => Term.closedWith fns k t && Term.closedListWith fns k ts

def Place.closedWith (fns : List SpecFn) (k : Term → Bool) : Place → Bool
  | .slot _ => true
  | .offset b i | .entry b i | .elem b i _ | .packedElem b i _ =>
    Place.closedWith fns k b && Term.closedWith fns k i
end

/-- Every spec function call in `t` resolves, with as many arguments as parameters, and calls nest
at most `fuel` deep, counting the bodies they unfold: `eval fns fuel t` never runs out of fuel. -/
def Term.Closed (fns : List SpecFn) : Nat → Term → Bool
  | 0 => Term.closedWith fns fun _ => false
  | n + 1 => Term.closedWith fns (Term.Closed fns n)

/-- `Term.Closed` of every term of a list. -/
def Term.ClosedList (fns : List SpecFn) (fuel : Nat) (ts : List Term) : Bool :=
  ts.all (Term.Closed fns fuel)

end SolidCore.Spec

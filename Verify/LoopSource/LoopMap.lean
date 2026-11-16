import SolidCore.Refinement.Generic.Source
import Verify.VC.Term

/-!
# solar-verify's loop-head names, read off the source's symbolic loop header

solar-verify names every value of a loop obligation by an SSA constant (`count@17` the count before
the loop, `count@27` and `i@28` the loop head's). The source loop bridge
(`SolidCore/Refinement/Generic/LoopErased.lean`) states a loop's obligations over the words of a
symbolic header state `H : SymState`, evaluated at a header valuation `σ : Val`. A `LoopMap`,
emitted by the compiler beside the obligations, says where each SSA name lives:

* `var x`: the local or parameter `x` in scope at the loop head (`Scopes.get? H.scopes x`);
* `slot s`: storage slot `s` at the loop head (`Writes.read H.writes (.lit s)`);
* `entrySlot s`: storage slot `s` when the call started (`old(...)`; `.init s`);
* `caller`: `msg.sender` (`H.caller`);
* `const v`: a name the source semantics does not model (`this`, `msg.value` of a nonpayable
  function), fixed to `v`; obligations hold for every value of their constants, so any value
  meeting the obligation's facts serves, and the facts are still checked at it.

`LoopMap.env M H σ` is then solar-verify's assignment at `σ`: each name the value of its word.
`Corr M H t w` says an SMT term `t` over the names denotes the word expression `w` operator by
operator, and `Corr.eval` is the **evaluation correspondence**: where `w` does not wrap (`NoWrap`),
`t` evaluates to `w`'s value. `holds_eq`, `holds_le` and `holds_lt` carry it to atoms, so an
obligation's goal over the names is a statement about the header's words.

A name the map does not place gets the value the binding supplies (`fr`); a map that names the wrong place makes the word lemmas a
binding states (`M.word H x = some w`, by `decide`) fail, so a stale or mismatched map is
rejected by the kernel, not trusted.
-/

namespace SolidCore.Verify.LoopMap

open SolidCore.Refinement.Generic SolidCore.Verify.VC

/-- Where an SSA name lives. -/
inductive Loc where
  | var (x : String)
  | slot (s : Nat)
  | entrySlot (s : Nat)
  | caller
  | const (v : Nat)
  deriving DecidableEq, Repr

/-- The word of a place at the header state `H`. -/
def Loc.word (H : SymState) : Loc → Option WExpr
  | .var x => Scopes.get? H.scopes x
  | .slot s => some (Writes.read H.writes (.lit s))
  | .entrySlot s => some (.init (s % wordSize))
  | .caller => some H.caller
  | .const v => some (.lit v)

/-- A loop's map from solar-verify's SSA names to places. -/
structure LoopMap where
  names : List (String × Loc)
  deriving DecidableEq, Repr

/-- The word an SSA name denotes at the header state `H`. -/
def LoopMap.word (M : LoopMap) (H : SymState) (x : String) : Option WExpr :=
  match M.names.lookup x with
  | some l => l.word H
  | none => none

/-- solar-verify's assignment at the header valuation `σ`: each placed name the value of its word,
each other name (`fr`) the value the binding supplies. -/
def LoopMap.env (M : LoopMap) (H : SymState) (fr : String → Int) (σ : Val) : Env where
  i x := match M.word H x with
    | some w => ((w.eval σ : Nat) : Int)
    | none => fr x
  b _ := False
  a _ _ := 0

theorem LoopMap.env_i {M : LoopMap} {H : SymState} {fr : String → Int} {σ : Val} {x : String}
    {w : WExpr} (h : M.word H x = some w) : (M.env H fr σ).i x = ((w.eval σ : Nat) : Int) := by
  simp [LoopMap.env, h]

theorem LoopMap.env_free {M : LoopMap} {H : SymState} {fr : String → Int} {σ : Val} {x : String}
    (h : M.word H x = none) : (M.env H fr σ).i x = fr x := by
  simp [LoopMap.env, h]

/-- No operator of `w` wraps around `2 ^ 256` at `σ`. -/
def NoWrap (σ : Val) : WExpr → Prop
  | .bin .add a b => a.eval σ + b.eval σ < wordSize ∧ NoWrap σ a ∧ NoWrap σ b
  | .bin .sub a b => b.eval σ ≤ a.eval σ ∧ NoWrap σ a ∧ NoWrap σ b
  | _ => True

/-- The SMT term `t` over solar-verify's names denotes the word `w` of `H`, operator by operator. -/
inductive Corr (M : LoopMap) (H : SymState) : Tm → WExpr → Prop
  | num {n : Nat} : n < wordSize → Corr M H (.num n) (.lit n)
  | var {x : String} {w : WExpr} : M.word H x = some w → Corr M H (.ivar x) w
  | add {a b : Tm} {wa wb : WExpr} :
      Corr M H a wa → Corr M H b wb → Corr M H (.app "+" [a, b]) (.bin .add wa wb)
  | sub {a b : Tm} {wa wb : WExpr} :
      Corr M H a wa → Corr M H b wb → Corr M H (.app "-" [a, b]) (.bin .sub wa wb)

theorem sub_mod {x y : Nat} (hy : y ≤ x) (hx : x < wordSize) :
    (x + (wordSize - y)) % wordSize = x - y := by
  have h : x + (wordSize - y) = (x - y) + wordSize := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **The evaluation correspondence**: where `w` does not wrap, `t` evaluates to `w`'s value. -/
theorem Corr.eval {M : LoopMap} {H : SymState} {fr : String → Int} {σ : Val} :
    ∀ {t : Tm} {w : WExpr}, Corr M H t w → NoWrap σ w →
      t.eval (M.env H fr σ) = .int ((w.eval σ : Nat) : Int)
  | _, _, .num hn, _ => by
    simp only [Tm.eval, WExpr.eval, Nat.mod_eq_of_lt hn]
  | _, _, .var h, _ => by
    simp only [Tm.eval, LoopMap.env_i h]
  | _, _, .add (wa := wa) (wb := wb) ca cb, hw => by
    obtain ⟨hs, ha, hb⟩ := hw
    have ea := Corr.eval (fr := fr) ca ha
    have eb := Corr.eval (fr := fr) cb hb
    simp only [Tm.eval, Tm.evalList, ea, eb, applyOp, Value.toInt, WExpr.eval, BinOp.eval,
      Nat.mod_eq_of_lt hs, Nat.cast_add]
  | _, _, .sub (wa := wa) (wb := wb) ca cb, hw => by
    obtain ⟨hs, ha, hb⟩ := hw
    have ea := Corr.eval (fr := fr) ca ha
    have eb := Corr.eval (fr := fr) cb hb
    have hlt := WExpr.eval_lt σ wa
    simp only [Tm.eval, Tm.evalList, ea, eb, applyOp, Value.toInt, WExpr.eval, BinOp.eval,
      sub_mod hs hlt, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hlt), Nat.cast_sub hs]

/-- `a = b` over the names holds exactly when the two words are equal. -/
theorem holds_eq {M : LoopMap} {H : SymState} {fr : String → Int} {σ : Val} {a b : Tm} {wa wb : WExpr}
    (ca : Corr M H a wa) (cb : Corr M H b wb) (ha : NoWrap σ wa) (hb : NoWrap σ wb) :
    (Tm.app "=" [a, b]).Holds (M.env H fr σ) ↔ wa.eval σ = wb.eval σ := by
  simp only [Tm.Holds, Tm.eval, Tm.evalList, Corr.eval ca ha, Corr.eval cb hb, applyOp,
    Value.eq, Value.toProp, Nat.cast_inj]

/-- `a <= b` over the names holds exactly when the words are so ordered. -/
theorem holds_le {M : LoopMap} {H : SymState} {fr : String → Int} {σ : Val} {a b : Tm} {wa wb : WExpr}
    (ca : Corr M H a wa) (cb : Corr M H b wb) (ha : NoWrap σ wa) (hb : NoWrap σ wb) :
    (Tm.app "<=" [a, b]).Holds (M.env H fr σ) ↔ wa.eval σ ≤ wb.eval σ := by
  simp only [Tm.Holds, Tm.eval, Tm.evalList, Corr.eval ca ha, Corr.eval cb hb, applyOp,
    Value.toInt, Value.toProp, Nat.cast_le]

/-- `a < b` over the names holds exactly when the words are so ordered. -/
theorem holds_lt {M : LoopMap} {H : SymState} {fr : String → Int} {σ : Val} {a b : Tm} {wa wb : WExpr}
    (ca : Corr M H a wa) (cb : Corr M H b wb) (ha : NoWrap σ wa) (hb : NoWrap σ wb) :
    (Tm.app "<" [a, b]).Holds (M.env H fr σ) ↔ wa.eval σ < wb.eval σ := by
  simp only [Tm.Holds, Tm.eval, Tm.evalList, Corr.eval ca ha, Corr.eval cb hb, applyOp,
    Value.toInt, Value.toProp, Nat.cast_lt]

end SolidCore.Verify.LoopMap

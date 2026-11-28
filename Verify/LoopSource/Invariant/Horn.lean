import Verify.LoopSource.Invariant.While

/-!
# `Horn.ok_transfer`: a `while` loop through its invariant, from source to its tree

solar-verify's `Horn.ok_transfer` (crates/verify/tests/cases/horn.sol, scored as `verify/horn`):

    function ok_transfer(uint256 n) public pure returns (uint256) {
        uint256 a = n; uint256 b = 0;
        while (a > 0) { a--; b++; }
        return b;
    }

`eraseLoopStmt` has no `while` case, so it erases to `none` (`counted_none`). This module erases it
through the invariant `I`: `b + a = n₀ ∧ n = n₀ ∧ _ret0 = 0` over the source header's words (the
source form of `n = a + b`, which Spacer proposed for the MIR loop), with the measure `μ = a`, which
the kernel checks (`obl`): the loop ends with `a = 0`, `b = n₀`, and `b++` never overflows.

* `hornFn`: the function as SolidCore's type checker leaves it (the solc-AST front end on
  `horn.sol`, then `TypeCheck.CheckedInput.contract`; restated, and compared with the checked
  contract by `fn_checked` in the stage module).
* `wd`: the loop's data, `horn_erased`: `eraseWhile` computes, by `rfl`, the tree `br`: return the
  argument word. `horn_runs`: `BodyRuns` of it, by `bodyRuns_of_eraseWhile` and `obl`.
* `horn_tree`: the call's tree is `Tret` (succeed, return `n`, no writes, no logs), the tree the
  cut-point certificate's obligations are stated against (`Verify.Phase3.Infer.HornOkTransfer.T`).
* Controls: a wrong exit word, a wrong invariant (`b = n` before the loop is false), and the
  counted-loop erasure, are refused.
-/

namespace Verify.LoopSource.Invariant.Horn
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Verify.LoopSource.Invariant

/-! ## The function, as the type checker leaves it -/

def s1 : Stmt := .assign (.var "n") (.castOp .uintCleanup 256 (.var "n"))
def declA : Stmt := .varDecl .uint256 "a" (some (.castOp .uintCleanup 256 (.var "n")))
def declB : Stmt := .varDecl .uint256 "b" (some (.word 0))
/-- `a > 0`. -/
def cnd : Expr := .binary .gt (.castOp .uintCleanup 256 (.var "a")) (.word 0)
/-- `{ a--; b++; }`. -/
def body : Stmt := .block [.exprStmt (.incDec .sub true (some (.uint 256)) (.var "a")),
  .exprStmt (.incDec .add true (some (.uint 256)) (.var "b"))]
def ret : Stmt := .returnValues [.castOp .uintCleanup 256 (.var "b")]
def hornBody : Stmt := .block [s1, .skip, .block [declA, declB, .whileLoop cnd body, ret]]

/-- `ok_transfer`, as the type checker leaves it. -/
def hornFn : FunctionDef :=
  { name := "ok_transfer", selector? := some 4244640165, payable := false,
    params := [{ name := "n", ty := Ty.uint256, isStorageRef := false }],
    paramAbiCleanups := [AbiCleanup.uint 256],
    returns := [{ name := "_ret0", ty := Ty.uint256, isStorageRef := false }],
    body := hornBody, dispatchId? := none }

/-- The erasure environment of `ok_transfer`: no storage, and no argument facts (`n` is a
`uint256`). -/
def env (ev : List EventDecl) (tbl : FunctionTable) : EraseEnv :=
  { fields := [], events := ev, tbl := tbl, facts := [] }

/-! ## The loop's data (untrusted; `check` recomputes it) -/

/-- The state before the loop: `b = 0`, `a = n`. -/
def S1 : SymState :=
  { scopes := [[("b", .lit 0), ("a", .arg 0)], [], [("n", .arg 0), ("_ret0", .lit 0)]],
    writes := [], logs := [], next := some 0 }

/-- The body's end at the header (`b, a, n, _ret0` are the words `1, 2, 3, 4`). -/
def S2 : SymState :=
  { scopes := [[("b", .bin .add (.arg 1) (.lit 1)), ("a", .bin .sub (.arg 2) (.lit 1))], [],
      [("n", .arg 3), ("_ret0", .arg 4)]],
    writes := [], logs := [] }

def wd : WhileData :=
  { S1 := S1, slots := [], k := 100, c := .bin .gt (.arg 2) (.lit 0),
    gs := [.bin .lt (.arg 2) (.lit 1), .bin .lt (.bin .add (.arg 1) (.lit 1)) (.arg 1)], S2 := S2,
    exit := [.arg 0, .lit 0, .arg 0, .lit 0] }

/-- The statement fuel: `loopFuel`, the body's `100` and the three statements around the loop. -/
def fuel : Nat := 2 ^ 256 + 108

/-- The function's tree: return the word `b` holds after the loop, `n`. -/
def br : Br :=
  .leaf (.returned { scopes := [[("n", .arg 0), ("_ret0", .lit 0)]], writes := [], logs := [] } [.arg 0] [])

/-- **The erasure computes.** -/
theorem horn_erased (ev : List EventDecl) (tbl : FunctionTable) :
    eraseWhile (env ev tbl) wd fuel hornFn.body (initState hornFn) = some br := rfl

/-! ## The invariant and its obligations -/

/-- The invariant over the header words `b = 1, a = 2, n = 3, _ret0 = 4`: `n = n₀`, `_ret0 = 0`,
`b + a = n₀` as integers. -/
def I (ρ σ : Val) : Prop :=
  (WExpr.arg 3).eval σ = (WExpr.arg 0).eval ρ ∧ (WExpr.arg 4).eval σ = 0 ∧
    (WExpr.arg 1).eval σ + (WExpr.arg 2).eval σ = (WExpr.arg 0).eval ρ

/-- The measure: `a`. -/
def μ (_ρ σ : Val) : Nat := (WExpr.arg 2).eval σ

theorem arg_extV (ρ : Val) (f : Nat → Nat) (i : Nat) :
    (WExpr.arg i).eval (extV ρ 1 4 f) =
      if i < 1 then (WExpr.arg i).eval ρ else if i - 1 < 4 then f (i - 1) % Generic.wordSize else 0 := by
  simp only [WExpr.eval, extV_getD]
  split_ifs <;> simp

theorem at_eq (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) (f : Nat → Nat) :
    wd.at_ (env ev tbl) ρ f = extV ρ 1 4 f := rfl

theorem head_eq (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) :
    headVal ρ (wd.base (env ev tbl)) wd.S1 wd.slots =
      extV ρ 1 4 (fun j => ([WExpr.lit 0, .arg 0, .arg 0, .lit 0].getD j (.lit 0)).eval ρ) := rfl

theorem stepV_eq (ρ : Val) (f : Nat → Nat) :
    wd.stepV (extV ρ 1 4 f) =
      fun j => ([WExpr.bin .add (.arg 1) (.lit 1), .bin .sub (.arg 2) (.lit 1), .arg 3, .arg 4].getD j
        (.lit 0)).eval (extV ρ 1 4 f) := rfl

theorem x_lt (ρ : Val) : (WExpr.arg 0).eval ρ < Generic.wordSize := WExpr.eval_lt ρ _

/-- Words of the header valuation, in normal form: the argument word `n` of `ρ` stays a word,
every fresh word is its value, and the word operations compute. -/
macro "hornw" : tactic => `(tactic| (
  simp only [I, μ, WhileData.exitθ, wd, eval_bin, eval_lit, arg_extV, BinOp.eval, Generic.wordSize,
    Nat.reducePow, Nat.reduceLT, Nat.reduceSub, Nat.reduceMod, Nat.lt_irrefl, Nat.zero_mod,
    List.getD_cons_zero, List.getD_cons_succ, ↓reduceIte, Nat.not_lt_zero, true_and, and_true] at * <;>
  (try split_ifs at * ) <;> omega))

/-- **The loop's obligations hold**: initiation, exit, no overflow, preservation and the
measure's fall, about words. -/
theorem obl (ev : List EventDecl) (tbl : FunctionTable) : Obl (env ev tbl) wd I μ where
  init ρ _ _ := by
    rw [head_eq]
    have hx := x_lt ρ
    hornw
  bound ρ _ _ := by
    rw [head_eq]
    have hx := x_lt ρ
    unfold loopFuel
    hornw
  exit ρ f _ _ hf hI hz := by
    rw [at_eq] at hI hz
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
    intro j hj
    have hl : wd.len = 4 := rfl
    rw [hl] at hj
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    all_goals hornw
  guards ρ f _ _ hf hI hnz := by
    rw [at_eq] at hI hnz ⊢
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
    intro g hg
    simp only [wd, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    all_goals hornw
  pres ρ f _ _ hf hI hnz := by
    rw [at_eq] at hI hnz
    rw [at_eq, at_eq, stepV_eq]
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
    hornw
  dec ρ f _ _ hf hI hnz := by
    rw [at_eq] at hI hnz
    rw [at_eq, at_eq, stepV_eq]
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
    hornw

/-! ## The body runs to its tree -/

/-- **`ok_transfer`'s body runs to `br`**, from the invariant's obligations. -/
theorem horn_runs (ev : List EventDecl) (tbl : FunctionTable) :
    BodyRuns (env ev tbl) fuel hornFn br :=
  bodyRuns_of_eraseWhile (obl ev tbl) (horn_erased ev tbl)

/-- The call's tree: succeed, return the argument word, no writes, no logs. -/
def Tret : Tree := .halt true (wordOBytes (.arg 0)) [] []

theorem horn_tree : brTree hornFn (argFacts [2 ^ 256 - 1] 0) br = some Tret := rfl

/-! ## Controls -/

/-- The counted-loop erasure refuses the `while` loop. -/
theorem counted_none (ev : List EventDecl) (tbl : FunctionTable) :
    eraseLoopStmt (env ev tbl) fuel hornFn.body (initState hornFn) = none := rfl

/-- The data with a wrong exit word: `b` ends at `n + 1`. -/
def wdBad : WhileData := { wd with exit := [.bin .add (.arg 0) (.lit 1), .lit 0, .arg 0, .lit 0] }

/-- The call with `n = 0` and empty storage. -/
def ρ0 : Val := ⟨[0], fun _ => 0, fun _ _ => 0, 0⟩

/-- **A wrong exit word is refused**: at `n = 0` the loop exits with `b = 0`, not `1`. -/
theorem wrong_exit (ev : List EventDecl) (tbl : FunctionTable) : ¬ Obl (env ev tbl) wdBad I μ := by
  intro h
  have hok : ρ0.Ok := fun _ => rfl
  have hK : (env ev tbl).facts.Hold ρ0 := fun _ h => absurd h List.not_mem_nil
  have hI : I ρ0 (wdBad.at_ (env ev tbl) ρ0 fun _ => 0) := by
    show I ρ0 (extV ρ0 1 4 fun _ => 0)
    exact ⟨rfl, rfl, rfl⟩
  have hz : wdBad.c.eval (wdBad.at_ (env ev tbl) ρ0 fun _ => 0) = 0 := by
    show (WExpr.bin .gt (.arg 2) (.lit 0)).eval (extV ρ0 1 4 fun _ => 0) = 0
    rfl
  have := h.exit ρ0 _ hok hK (fun _ => Nat.two_pow_pos 256) hI hz 0 (by decide)
  exact absurd this (by decide)

/-- **A wrong invariant is refused**: `b = n₀` at the header fails initiation at `n₀ = 1`. -/
theorem wrong_inv (ev : List EventDecl) (tbl : FunctionTable) :
    ¬ Obl (env ev tbl) wd (fun ρ σ => (WExpr.arg 1).eval σ = (WExpr.arg 0).eval ρ) μ := by
  intro h
  have := h.init ⟨[1], fun _ => 0, fun _ _ => 0, 0⟩ (fun _ => rfl) (fun _ h => absurd h List.not_mem_nil)
  rw [head_eq] at this
  exact absurd this (by decide)

end Verify.LoopSource.Invariant.Horn

/-- info: 'Verify.LoopSource.Invariant.Horn.horn_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.Horn.horn_runs

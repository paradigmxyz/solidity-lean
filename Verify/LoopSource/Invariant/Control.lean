import SolidCore.Refinement.KernelRfl
import Verify.LoopSource.Invariant.While
import Verify.LoopSource.Invariant.ControlSource

/-!
# `Control.ok_while` and its twins: a `while` loop through its invariant, source side

solar-verify's `Control` (crates/verify/tests/cases/control.sol, scored as `verify/control`) has three
functions with the same body, `ok_while` (whose loop carries `@custom:invariant i <= n`),
`ok_no_invariant` and `bad_no_invariant` (whose invariant inference must find):

    uint256 i = 0;
    while (i < n) { i++; }
    return i;

This module erases the body through the invariant `i ≤ n₀ ∧ n = n₀ ∧ _ret0 = 0` and the measure
`n - i` (`obl`, checked by the kernel), so the body runs to the tree "return `n`" (`ctl_runs`,
`ctl_tree`). `fns_checked` proves in the kernel that the checked contract's functions at the three
selectors are `ctlFn` with that body. The other functions of `Control` (`for` loops with `break` and
`continue`, `s += i`) are outside `eraseWhile`.
-/

namespace Verify.LoopSource.Invariant.Control
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Verify.LoopSource.Invariant

/-! ## The functions, as the type checker leaves them -/

def s1 : Stmt := .assign (.var "n") (.castOp .uintCleanup 256 (.var "n"))
def declI : Stmt := .varDecl .uint256 "i" (some (.word 0))
/-- `i < n`. -/
def cnd : Expr := .binary .lt (.castOp .uintCleanup 256 (.var "i")) (.castOp .uintCleanup 256 (.var "n"))
/-- `{ i++; }`. -/
def body : Stmt := .block [.exprStmt (.incDec .add true (some (.uint 256)) (.var "i"))]
def ret : Stmt := .returnValues [.castOp .uintCleanup 256 (.var "i")]
def ctlBody : Stmt := .block [s1, .skip, .block [declI, .whileLoop cnd body, ret]]

/-- A function of `Control` with this body. -/
def ctlFn (name : String) (sel : Nat) : FunctionDef :=
  { name := name, selector? := some sel, payable := false,
    params := [{ name := "n", ty := Ty.uint256, isStorageRef := false }],
    paramAbiCleanups := [AbiCleanup.uint 256],
    returns := [{ name := "_ret0", ty := Ty.uint256, isStorageRef := false }],
    body := ctlBody, dispatchId? := none }

def env (ev : List EventDecl) (tbl : FunctionTable) : EraseEnv :=
  { fields := [], events := ev, tbl := tbl, facts := [] }

/-! ## The loop's data (untrusted; `check` recomputes it) -/

def S1 : SymState :=
  { scopes := [[("i", .lit 0)], [], [("n", .arg 0), ("_ret0", .lit 0)]], writes := [], logs := [] }

/-- The body's end at the header (`i, n, _ret0` are the words `1, 2, 3`). -/
def S2 : SymState :=
  { scopes := [[("i", .bin .add (.arg 1) (.lit 1))], [], [("n", .arg 2), ("_ret0", .arg 3)]],
    writes := [], logs := [] }

def wd : WhileData :=
  { S1 := S1, slots := [], k := 100, c := .bin .lt (.arg 1) (.arg 2),
    gs := [.bin .lt (.bin .add (.arg 1) (.lit 1)) (.arg 1)], S2 := S2,
    exit := [.arg 0, .arg 0, .lit 0] }

def fuel : Nat := 2 ^ 256 + 108

/-- The tree of the body: return `n`. -/
def br : Br :=
  .leaf (.returned { scopes := [[("n", .arg 0), ("_ret0", .lit 0)]], writes := [], logs := [] } [.arg 0])

theorem ctl_erased (name : String) (sel : Nat) (ev : List EventDecl) (tbl : FunctionTable) :
    eraseWhile (env ev tbl) wd fuel (ctlFn name sel).body (initState (ctlFn name sel)) = some br := rfl

/-! ## The invariant and its obligations -/

/-- `n = n₀`, `_ret0 = 0`, `i ≤ n₀`. -/
def I (ρ σ : Val) : Prop :=
  (WExpr.arg 2).eval σ = (WExpr.arg 0).eval ρ ∧ (WExpr.arg 3).eval σ = 0 ∧
    (WExpr.arg 1).eval σ ≤ (WExpr.arg 0).eval ρ

/-- The measure `n - i`. -/
def μ (_ρ σ : Val) : Nat := (WExpr.arg 2).eval σ - (WExpr.arg 1).eval σ

theorem arg_extV (ρ : Val) (f : Nat → Nat) (i : Nat) :
    (WExpr.arg i).eval (extV ρ 1 3 f) =
      if i < 1 then (WExpr.arg i).eval ρ else if i - 1 < 3 then f (i - 1) % Generic.wordSize else 0 := by
  simp only [WExpr.eval, extV_getD]
  split_ifs <;> simp

theorem at_eq (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) (f : Nat → Nat) :
    wd.at_ (env ev tbl) ρ f = extV ρ 1 3 f := rfl

theorem head_eq (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) :
    headVal ρ (wd.base (env ev tbl)) wd.S1 wd.slots =
      extV ρ 1 3 (fun j => ([WExpr.lit 0, .arg 0, .lit 0].getD j (.lit 0)).eval ρ) := rfl

theorem stepV_eq (ρ : Val) (f : Nat → Nat) :
    wd.stepV (extV ρ 1 3 f) =
      fun j => ([WExpr.bin .add (.arg 1) (.lit 1), .arg 2, .arg 3].getD j (.lit 0)).eval (extV ρ 1 3 f) := rfl

theorem x_lt (ρ : Val) : (WExpr.arg 0).eval ρ < Generic.wordSize := WExpr.eval_lt ρ _

/-- Words of the header valuation in normal form, then linear arithmetic. -/
macro "ctlw" : tactic => `(tactic| (
  simp only [I, μ, WhileData.exitθ, wd, eval_bin, eval_lit, arg_extV, BinOp.eval, Generic.wordSize,
    Nat.reducePow, Nat.reduceLT, Nat.reduceSub, Nat.reduceMod, Nat.lt_irrefl, Nat.zero_mod,
    List.getD_cons_zero, List.getD_cons_succ, ↓reduceIte, Nat.not_lt_zero, true_and, and_true] at * <;>
  (try split_ifs at * ) <;> omega))

/-- **The loop's obligations hold.** -/
theorem obl (ev : List EventDecl) (tbl : FunctionTable) : Obl (env ev tbl) wd I μ where
  init ρ _ _ := by
    rw [head_eq]
    have hx := x_lt ρ
    ctlw
  bound ρ _ _ := by
    rw [head_eq]
    have hx := x_lt ρ
    unfold loopFuel
    ctlw
  exit ρ f _ _ hf hI hz := by
    rw [at_eq] at hI hz
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2
    intro j hj
    have hl : wd.len = 3 := rfl
    rw [hl] at hj
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    all_goals ctlw
  guards ρ f _ _ hf hI hnz := by
    rw [at_eq] at hI hnz ⊢
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2
    intro g hg
    simp only [wd, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    ctlw
  pres ρ f _ _ hf hI hnz := by
    rw [at_eq] at hI hnz
    rw [at_eq, at_eq, stepV_eq]
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2
    ctlw
  dec ρ f _ _ hf hI hnz := by
    rw [at_eq] at hI hnz
    rw [at_eq, at_eq, stepV_eq]
    have hx := x_lt ρ
    have h0 := hf 0; have h1 := hf 1; have h2 := hf 2
    ctlw

/-- **The body runs to `br`**, for each of the three functions. -/
theorem ctl_runs (name : String) (sel : Nat) (ev : List EventDecl) (tbl : FunctionTable) :
    BodyRuns (env ev tbl) fuel (ctlFn name sel) br :=
  bodyRuns_of_eraseWhile (obl ev tbl) (ctl_erased name sel ev tbl)

/-- The call's tree: succeed, return the argument word. -/
def Tret : Tree := .halt true (wordOBytes (.arg 0)) [] []

theorem ctl_tree (name : String) (sel : Nat) : brTree (ctlFn name sel) (argFacts [2 ^ 256 - 1] 0) br = some Tret := rfl

/-! ## The checked contract -/

def contract? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract :=
  SolidCore.Solidity.TypeCheck.CheckedInput.contract ControlSrc.importedSourceUnit "Control"

def selSig0 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "ok_while(uint256)"

kernel_rfl selSig0_eq selSig0 1081275856

def selSig1 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "ok_no_invariant(uint256)"

kernel_rfl selSig1_eq selSig1 1883199284

def selSig2 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "bad_no_invariant(uint256)"

kernel_rfl selSig2_eq selSig2 426309362

def selSig3 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "bad_noninductive_candidate(uint256)"

kernel_rfl selSig3_eq selSig3 1224582662

def selSig4 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "ok_break(uint256)"

kernel_rfl selSig4_eq selSig4 216874927

def selSig5 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "bad_break(uint256)"

kernel_rfl selSig5_eq selSig5 4165418621

def selSig6 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "ok_continue(uint256)"

kernel_rfl selSig6_eq selSig6 1970511756

def selSig7 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "ok_early_return(uint256)"

kernel_rfl selSig7_eq selSig7 1939733917

def selSig8 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "bad_decreases(uint256)"

kernel_rfl selSig8_eq selSig8 2900664096

def selSig9 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "bad_assert_ghost(uint256)"

kernel_rfl selSig9_eq selSig9 1244794278

def selSig10 : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "ok_require_assume(uint256)"

kernel_rfl selSig10_eq selSig10 3239613908

/-- `ABI.selectorFromSignature`, with the contract's signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "ok_while(uint256)" then 1081275856
  else if s = "ok_no_invariant(uint256)" then 1883199284
  else if s = "bad_no_invariant(uint256)" then 426309362
  else if s = "bad_noninductive_candidate(uint256)" then 1224582662
  else if s = "ok_break(uint256)" then 216874927
  else if s = "bad_break(uint256)" then 4165418621
  else if s = "ok_continue(uint256)" then 1970511756
  else if s = "ok_early_return(uint256)" then 1939733917
  else if s = "bad_decreases(uint256)" then 2900664096
  else if s = "bad_assert_ghost(uint256)" then 1244794278
  else if s = "ok_require_assume(uint256)" then 3239613908
  else ABI.selectorFromSignature s

theorem selector_eq : ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selSig0_eq
  · split
    · next h => subst h; exact selSig1_eq
    · split
      · next h => subst h; exact selSig2_eq
      · split
        · next h => subst h; exact selSig3_eq
        · split
          · next h => subst h; exact selSig4_eq
          · split
            · next h => subst h; exact selSig5_eq
            · split
              · next h => subst h; exact selSig6_eq
              · split
                · next h => subst h; exact selSig7_eq
                · split
                  · next h => subst h; exact selSig8_eq
                  · split
                    · next h => subst h; exact selSig9_eq
                    · split
                      · next h => subst h; exact selSig10_eq
                      · rfl

/-- The checked contract's functions at the three selectors, and its storage fields. -/
def found? : Option (List (Option FunctionDef) × List StorageField) :=
  match contract? with
  | .ok c => some ([1081275856, 1883199284, 426309362].map c.core.findFunctionBySelector?,
      c.core.storageFields)
  | .error _ => none

kernel_rfl found_eq found? (some ([some (ctlFn "ok_while" 1081275856),
  some (ctlFn "ok_no_invariant" 1883199284), some (ctlFn "bad_no_invariant" 426309362)], []))
  using selector_eq

/-- **The checked contract's `ok_while`, `ok_no_invariant` and `bad_no_invariant` are `ctlFn`**, and
the contract has no storage. -/
theorem fns_checked {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core.findFunctionBySelector? 1081275856 = some (ctlFn "ok_while" 1081275856) ∧
    c.core.findFunctionBySelector? 1883199284 = some (ctlFn "ok_no_invariant" 1883199284) ∧
    c.core.findFunctionBySelector? 426309362 = some (ctlFn "bad_no_invariant" 426309362) ∧
    c.core.storageFields = [] := by
  have h := found_eq
  unfold found? at h
  rw [hc] at h
  simp only [List.map_cons, List.map_nil, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2⟩

/-- **Each of the three runs, in the checked contract's environment, to "return `n`"**: the
premises `hb` and `hT` of `loop_stage` / `Join.while_stage`. -/
theorem checked_runs {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) (name : String)
    (sel : Nat) :
    BodyRuns { envOf c.core with facts := argFacts [2 ^ 256 - 1] 0 } fuel (ctlFn name sel) br ∧
      brTree (ctlFn name sel) (argFacts [2 ^ 256 - 1] 0) br = some Tret := by
  have hE : ({ envOf c.core with facts := argFacts [2 ^ 256 - 1] 0 } : EraseEnv) =
      env c.core.eventDecls c.core.table := by
    simp only [envOf, env, (fns_checked hc).2.2.2]
    rfl
  rw [hE]
  exact ⟨ctl_runs name sel _ _, ctl_tree name sel⟩

/-! ## Controls -/

/-- Without the bound in the invariant the exit word is not determined: `n = n₀ ∧ _ret0 = 0` alone
does not give `i = n₀` at the exit (`i = n₀ + 1` also exits). -/
theorem weak_inv (ev : List EventDecl) (tbl : FunctionTable) :
    ¬ Obl (env ev tbl) wd (fun ρ σ => (WExpr.arg 2).eval σ = (WExpr.arg 0).eval ρ ∧
      (WExpr.arg 3).eval σ = 0) μ := by
  intro h
  have hx := h.exit ⟨[0], fun _ => 0, fun _ _ => 0, 0⟩ (fun j => if j = 0 then 1 else 0) (fun _ => rfl)
    (fun _ h => absurd h List.not_mem_nil) (fun j => by split <;> decide)
    (by rw [at_eq]; exact ⟨rfl, rfl⟩) (by rw [at_eq]; rfl) 0 (by decide)
  exact absurd hx (by decide)

end Verify.LoopSource.Invariant.Control

/-- info: 'Verify.LoopSource.Invariant.Control.ctl_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.Control.ctl_runs

/-- info: 'Verify.LoopSource.Invariant.Control.checked_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.Control.checked_runs

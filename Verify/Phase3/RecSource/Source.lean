import Verify.Phase3.RecSource.Ast
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Generic.LoopRun

/-!
# RecSum in SolidCore: the checked contract

`contract?` is SolidCore's type checker on RecSum.sol's solc AST. The kernel checks (`shape_eq`, on
copies of the type checker that read the selector from `selectorTable`) that it has no storage
fields and no events, that its function of selector `total(uint256)` is `totalFn`, and that its
table holds `sum` as `sumFn`, whose body calls `sum` itself at `n - 1`.
-/

namespace Verify.Phase3.RecSource
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic

/-- SolidCore's checked `RecSum`. -/
def contract? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract :=
  SolidCore.Solidity.TypeCheck.CheckedInput.contract Verify.Phase3.RecSource.Ast.importedSourceUnit "RecSum"

/-- The selector of `total(uint256)`. -/
def totalSel : Nat := 0xb119ebfe

def selTotal : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "total(uint256)"
kernel_rfl selTotal_eq selTotal 2971266046

/-- `ABI.selectorFromSignature`, with RecSum's signature by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "total(uint256)" then 2971266046 else ABI.selectorFromSignature s

theorem selector_eq : ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split_ifs <;> subst_vars
  exacts [selTotal_eq, rfl]

/-- The table name of the internal function `sum`. -/
def sumName : String := "__internal_sum(uint256)#[SolidCore.Solidity.Ty.uint 256]"

/-- `n` cleaned to 256 bits. -/
def cn : Expr := .castOp .uintCleanup 256 (.var "n")

/-- The call of `sum` that a body makes: its argument `arg` in `_ic_arg_0`, its result in
`_ret_sum_0`, then `_sol_hoist_0 = _ret_sum_0`. -/
def callBlock (arg : Expr) : Stmt :=
  .block [.varDecl .uint256 "_ic_arg_0" (some arg), .varDecl .uint256 "_ret_sum_0" none,
    .captureReturn ["_ret_sum_0"] (.internalCall ["_ret_sum_0"] sumName [.var "_ic_arg_0"]),
    .assign (.var "_sol_hoist_0") (.var "_ret_sum_0")]

/-- `sum`'s argument at its recursive call: `n - 1`, cleaned. -/
def recArg : Expr :=
  .castOp .uintCleanup 256 (.castOp .uintCleanup 256 (.binary .sub cn (.word 1)))

/-- `if (n == 0) return 0;` -/
def baseIf : Stmt := .ifElse (.binary .eq cn (.word 0)) (.returnValues [.word 0]) .skip

/-- `return n + _sol_hoist_0;` -/
def retAdd : Stmt :=
  .returnValues [.castOp .uintCleanup 256 (.castOp .uintCleanup 256
    (.binary .add cn (.castOp .uintCleanup 256 (.var "_sol_hoist_0"))))]

/-- **`sum`'s body**, as the type checker leaves it. -/
def sumBody : Stmt :=
  .block [.assign (.var "n") cn, .skip,
    .block [baseIf, .varDecl .uint256 "_sol_hoist_0" none, callBlock recArg, retAdd]]

/-- **`total`'s body**, as the type checker leaves it. -/
def totalBody : Stmt :=
  .block [.assign (.var "n") cn, .skip,
    .block [.requireStmt (.binary .le cn (.word 64)) none, .varDecl .uint256 "_sol_hoist_0" none,
      callBlock cn, .returnValues [.castOp .uintCleanup 256 (.var "_sol_hoist_0")]]]

def nDecl : BindingDecl := { name := "n", ty := Ty.uint256, isStorageRef := false }
def retDecl : BindingDecl := { name := "_ret0", ty := Ty.uint256, isStorageRef := false }

/-- `total`, as the type checker leaves it. -/
def totalFn : FunctionDef :=
  { name := "total", selector? := some 2971266046, payable := false, params := [nDecl],
    paramAbiCleanups := [AbiCleanup.uint 256], returns := [retDecl], body := totalBody,
    dispatchId? := none }

/-- `sum`, as the type checker leaves it. -/
def sumFn : InternalFunction :=
  { name := sumName, params := [nDecl], returns := [retDecl], body := sumBody, id? := none }

/-- What the statement reads of the checked contract. -/
def shape? : Option (List StorageField × List EventDecl × Option FunctionDef × Option InternalFunction) :=
  match contract? with
  | .ok c => some (c.core.storageFields, c.core.eventDecls, c.core.findFunctionBySelector? totalSel,
      c.core.table.lookup? sumName)
  | .error _ => none

kernel_rfl shape_eq shape? (some ([], [], some totalFn, some sumFn)) using selector_eq

theorem shape_of {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core.storageFields = [] ∧ c.core.eventDecls = [] ∧
      c.core.findFunctionBySelector? totalSel = some totalFn ∧ c.core.table.lookup? sumName = some sumFn := by
  have h := shape_eq
  unfold shape? at h
  rw [hc] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h

theorem contract_ok : ∃ c, contract? = .ok c := by
  have h := shape_eq
  unfold shape? at h
  cases hc : contract? with
  | ok c => exact ⟨c, rfl⟩
  | error _ => rw [hc] at h; simp at h

end Verify.Phase3.RecSource

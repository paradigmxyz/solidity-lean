import SolidCore.Refinement.KernelRfl
import Verify.LoopSource.Invariant.Join
import Verify.LoopSource.Invariant.Horn
import Verify.LoopSource.Invariant.HornSource
import Verify.Phase3.Infer.Horn.Obl

/-!
# `Horn.ok_transfer` past the source side: source to MIR through both invariants

The checked contract is SolidCore's type checker on the solc-AST front end's `Horn`
(`HornSource.lean`); `found_eq` proves in the kernel that its function at selector `0xfd0011a5` is
`Horn.hornFn` and that it has no storage. Then:

* the source side: `ok_transfer`'s body runs to `Horn.br` through the loop invariant
  `b + a = n₀` and the measure `a` (`Horn.obl`, `bodyRuns_of_eraseWhile`), so its tree is `Tret`:
  succeed, return `n`;
* the MIR side: solar's lowered MIR (`HornOkTransfer.stage0`) has a cut-point certificate that
  checks (`HornOkTransfer.leaves`), with obligations against the same tree proved from the invariant
  `b ≤ n ∧ n = a + b` and the measure `a` that Spacer proposed (`HornOkTransfer.obl`).

`horn_stage` composes them by `Join.while_stage`: on every valid call, under every oracle the flags
allow, the MIR runs to the source's observable. `horn_certified` is `Join.while_certified` for this
function: the driver's `Shapes.Certified`, from the stages the pipeline proves for every program
(the backend's MIR-to-EVM-IR stage, the assembler's loop checker) and a measure bridge of the final
EVM IR, which are its remaining premises.
-/

namespace Verify.LoopSource.Invariant.HornStage
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar Verify.LoopSource.Equiv
open Verify.LoopSource.Invariant Verify.LoopSource.Invariant.Horn

/-- SolidCore's checked `Horn`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract HornSrc.importedSourceUnit "Horn"

/-- The selector of `ok_transfer(uint256)`. -/
abbrev sel : Nat := 0xfd0011a5

def selSigOk : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "ok_transfer(uint256)"

kernel_rfl selSigOk_eq selSigOk sel

def selSigBad : SolidCore.Solidity.Shared.Word := ABI.selectorFromSignature "bad_transfer(uint256)"

kernel_rfl selSigBad_eq selSigBad 413447281

/-- `ABI.selectorFromSignature`, with the contract's signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "ok_transfer(uint256)" then sel
  else if s = "bad_transfer(uint256)" then 413447281
  else ABI.selectorFromSignature s

theorem selector_eq : ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selSigOk_eq
  · split
    · next h => subst h; exact selSigBad_eq
    · rfl

/-- The checked contract's function at `sel`, and its storage fields. -/
def found? : Option (Option FunctionDef × List StorageField) :=
  match contract? with
  | .ok c => some (c.core.findFunctionBySelector? sel, c.core.storageFields)
  | .error _ => none

kernel_rfl found_eq found? (some (some hornFn, [])) using selector_eq

/-- **The checked contract's `ok_transfer` is `hornFn`**, and the contract has no storage. -/
theorem fn_checked {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core.findFunctionBySelector? sel = some hornFn ∧ c.core.storageFields = [] := by
  have h := found_eq
  unfold found? at h
  rw [hc] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h

theorem contract_ok : ∃ c, contract? = .ok c := by
  have h := found_eq
  unfold found? at h
  revert h
  cases contract? with
  | ok c => exact fun _ => ⟨c, rfl⟩
  | error _ => exact fun h => absurd h (by simp)

/-- The erasure environment `loop_stage` takes is `Horn.env`. -/
theorem env_eq {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ({ envOf c.core with facts := argFacts [256] 0 } : EraseEnv) =
      Horn.env c.core.eventDecls c.core.table := by
  simp only [envOf, Horn.env, (fn_checked hc).2]
  rfl

/-- The source's tree is the tree of the cut-point certificate's obligations. -/
theorem tree_same : Tret = Verify.Phase3.Infer.HornOkTransfer.T := rfl

/-- **`ok_transfer`, source to MIR**: through the source loop's invariant and the MIR loop's
cut-point certificate, every valid call of the checked contract runs, under every oracle the flags
allow, on solar's lowered MIR to the source's observable. -/
theorem horn_stage {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (o : Oracle)
    (ho : SourceAsk .off o) :
    Stage (solidCoreRuntime Horn.fuel) (mirSem o) c Verify.Phase3.Infer.HornOkTransfer.stage0
      (SelCall sel hornFn [256]) := by
  have hE := env_eq hc
  refine Join.while_stage (by decide) (fn_checked hc).1 rfl rfl (hE ▸ Horn.obl _ _)
    (hE ▸ horn_erased _ _) horn_tree Verify.Phase3.Infer.HornOkTransfer.leaves
    Verify.Phase3.Infer.HornOkTransfer.obl (fun _ _ _ => trivial) (fun ρ _ => by rw [tree_same]) o ho

/-- **`ok_transfer` certified, from the pipeline's remaining stages**: `Join.while_certified` for
this function, with the source side through the source invariant and the MIR side through the
cut-point certificate discharged; what is left is what the pipeline proves for every program (the
backend's MIR-to-EVM-IR stage and the assembler's loop checker) and a measure bridge of the final
EVM IR for the gas bound. `Allowed` and `Post` are checked on the tree `Tret`. -/
theorem horn_certified {c : TypeCheck.CheckedContract} (hc : contract? = .ok c)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat}
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle)
      Verify.Phase3.Infer.HornOkTransfer.stage0 q scope)
    (hscope : ∀ call, SelCall sel hornFn [256] call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    {Valid : Call → Prop} {Allowed Post : Call → Observable → Prop}
    (hsub : ∀ call, Valid call → SelCall sel hornFn [256] call) (hinh : ∃ call, Valid call)
    (hAl : OnTree sel hornFn [256] Tret Allowed) (hP : OnTree sel hornFn [256] Tret Post)
    {R : LoopRecord} {E B Xs M : Nat}
    (loops : ∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B Xs M)
    (hfit : AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M) < 2 ^ 64) :
    Shapes.Certified (solidCoreRuntime Horn.fuel) c code Valid Allowed Post
      (fun _ => AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M)) := by
  have hE := env_eq hc
  exact Join.while_certified Horn.fuel c sel hornFn [256] br Tret (by decide) (fn_checked hc).1 rfl rfl
    wd I μ (hE ▸ Horn.obl _ _) (hE ▸ horn_erased _ _) horn_tree
    Verify.Phase3.Infer.HornOkTransfer.cut .off Verify.Phase3.Infer.HornOkTransfer.stage0
    Verify.Phase3.Infer.HornOkTransfer.le Verify.Phase3.Infer.HornOkTransfer.li
    Verify.Phase3.Infer.HornOkTransfer.leaves Verify.Phase3.Infer.HornOkTransfer.T
    (fun _ => Inv.recOf Verify.Phase3.Infer.HornOkTransfer.I Verify.Phase3.Infer.HornOkTransfer.μ) id
    (fun _ => True) (fun _ => True) Verify.Phase3.Infer.HornOkTransfer.obl (fun _ _ _ => trivial)
    (fun ρ _ => by rw [tree_same]) q code scope cert mx backend hscope asm Valid Allowed Post hsub hinh
    hAl hP R E B Xs M loops hfit

end Verify.LoopSource.Invariant.HornStage

/-- info: 'Verify.LoopSource.Invariant.HornStage.horn_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.HornStage.horn_stage

/-- info: 'Verify.LoopSource.Invariant.HornStage.horn_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.HornStage.horn_certified

/-- info: 'Verify.LoopSource.Invariant.HornStage.contract_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.HornStage.contract_ok

import Verify.LoopSource.AssertImport
import SolidCore.Refinement.Generic.LoopRun
import Verify.Shapes

/-!
# The driver Statement's expected type for any function whose body runs to a tree

The certify driver publishes `Shapes.Certified (source_sem fuel) c code valid allowed post gas`
(`tools/certify/final.py`). For a contract whose source semantics is `solidCoreRuntime`, the
function at selector `sel` is `fn`, and its arguments have ABI widths `ws`, this module states
the link's expected type, `GenericLink`, for every contract, function, body and tree.

A loop route proves `BodyRuns` (`LoopRun.lean`) of the function's body for a loop-free tree `b`:
some route through supplied loop invariants and measures (`ForObl` / `WhileObl` and
`forLoop_of_erased` / `whileLoop_of_erased`) gives the body's run, loop included, as `b`'s leaves.
From that, `GenericLink` gives the whole Statement, with:

* `SelCall sel fn ws` as the valid calls: `sel` with clean argument words, no value and any storage;
* the allowed statuses and postcondition checked on the tree `T` that `brTree` makes of `b`
  (`OnTree`), a finite, loop-free check;
* the Statement's two bytecode obligations, `Shapes.Equiv` and `Shapes.Resources`, as premises.
  Nothing in a source loop's proof discharges them; they are the MIR/EVM side of the pipeline,
  which the gas lane's fixed-fuel stage feeds.

This module imports no proof of the link, and the check at the end fails the build if it does.
-/

namespace Verify.LoopSource.Generic
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- The call of selector `sel` with argument words `args` from storage `σ`, with no value. -/
def selCall (sel : Nat) (σ : List (Nat × Nat)) (args : List Nat) : Call :=
  { calldata := Abi.calldata sel args, callvalue := 0, storage := σ }

/-- The argument words a call of `fn` with ABI widths `ws` may take. -/
def ArgsOk (fn : FunctionDef) (ws : List Nat) (args : List Nat) : Prop :=
  args.length = fn.params.length ∧ (∀ a ∈ args, a < 2 ^ 256) ∧ argsClean ws args = true

/-- **The valid calls**: selector `sel` with clean argument words, no value and any storage. -/
def SelCall (sel : Nat) (fn : FunctionDef) (ws : List Nat) (call : Call) : Prop :=
  ∃ σ args, ArgsOk fn ws args ∧ call = selCall sel σ args

/-- `Q` holds of the tree's observable on every valid call. -/
def OnTree (sel : Nat) (fn : FunctionDef) (ws : List Nat) (T : Tree)
    (Q : Call → Observable → Prop) : Prop :=
  ∀ (σ : List (Nat × Nat)) args, ArgsOk fn ws args →
    Q (selCall sel σ args) (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs

/-- **The generic whole-Statement link.** For every checked contract `c`, statement fuel, function
`fn` at selector `sel` with word arguments of widths `ws` and word returns, and every tree `b` whose
leaves the body runs to (`BodyRuns`, the loop route's product), with `T` the tree `brTree`
makes of `b`: the allowed statuses and postcondition on `T`, and the bytecode's equivalence and
resources, give the driver's Statement. -/
def GenericLink : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (code : ByteArray) (Allowed Post : Call → Observable → Prop) (G : Call → Nat),
      OnTree sel fn ws T Allowed → OnTree sel fn ws T Post →
      Shapes.Equiv (solidCoreRuntime fuel) c code (SelCall sel fn ws) →
      Shapes.Resources (solidCoreRuntime fuel) c code (SelCall sel fn ws) G →
      Shapes.Certified (solidCoreRuntime fuel) c code (SelCall sel fn ws) Allowed Post G

end Verify.LoopSource.Generic


/-- info: Verify.LoopSource.Generic.Link imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.Generic.Link

/-- info: Verify.LoopSource.Proof.LoopErased imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.Proof.LoopErased


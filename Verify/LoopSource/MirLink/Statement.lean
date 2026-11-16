import Verify.LoopSource.RC.Headline
import Contracts.VerifyCounter.Source

/-!
# The driver Statement's expected type for Counter.bump's loop, stated apart from its proof

The certify driver publishes, for a contract of kind `certified`, the statement
`Shapes.Certified (source_sem fuel) c code valid allowed post gas` (`tools/certify/final.py`),
where `c` is the checked contract (`contract = .ok c`) and `code` the runtime bytes it bound.
Counter's constructor takes `uint256 _limit`, so its source semantics is `solidCoreRuntime`
(`source_sem`): SolidCore's ABI dispatcher from the call's storage. Its fuel is
`2 ^ 256 + 8`, and its valid calls are `BumpCall` (`Contracts/VerifyCounter/Source.lean`).

This module states what links the loop route's source theorem to that Statement. It imports only
the headline (`RC/Headline.lean`: the source theorem's type) and Counter's checked source
(`Contracts.VerifyCounter.Source`: the type checker's `contract?`, `bumpFn`, `BumpCall`). It
never imports the loop route's proof or the link's proof, and the `#assert_not_imported` checks
below fail the build if it ever does.

* `OnTree Q`: `Q` holds of the observable of bump's tree `brTree bumpFn (argFacts [256] 0) bumpBr`
  on every call `bump(a)`, from every storage. The tree is loop-free, so this is the finite check
  the driver's specification proof makes of any loop-free function.
* `StatementLink`: from the headline, for any runtime bytes, allowed statuses, postcondition and gas
  bound, the allowed statuses and postcondition on the tree, and the Statement's two bytecode
  obligations (`Shapes.Equiv` and `Shapes.Resources` of `code`), give the whole Statement
  `Shapes.Certified (solidCoreRuntime fuel) c code BumpCall Allowed Post G`. Termination and the
  specification, the Statement's source half, come from the loop theorem alone. The two bytecode
  obligations stay premises: no part of the loop's source proof discharges them.
* `StatementSourceHalf`: the Statement's source half, with bump's postcondition `BumpPost`
  (solar-verify's `count == old(count) + n` under the `require`).
-/

namespace Verify.LoopSource.MirLink
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source
open Verify.LoopSource.RC.Headline

/-- A call of `bump(a)` from storage `σ`. -/
def bumpCall (σ : List (Nat × Nat)) (a : Nat) : Call :=
  { calldata := Abi.calldata bumpSel [a], callvalue := 0, storage := σ }

/-- `Q` holds of the observable of bump's tree on every call `bump(a)`, from every storage. -/
def OnTree (Q : Call → Observable → Prop) : Prop :=
  ∀ T, brTree bumpFn (argFacts [256] 0) bumpBr = some T → ∀ (σ : List (Nat × Nat)) (a : Nat),
    a < 2 ^ 256 →
      Q (bumpCall σ a) (T.eval ⟨[a], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs

/-- The Statement's source semantics, as the driver names it (`source_sem`), at its fuel. -/
abbrev stmtSem : SolarTV.Sem := solidCoreRuntime Contracts.VerifyCounter.Source.fuel

/-- **The whole-Statement link**: the headline, the allowed statuses and postcondition on the tree,
and the bytecode's equivalence and resources give the driver's Statement. -/
def StatementLink : Prop :=
  CounterBumpLoopHeadline →
    ∀ (code : ByteArray) (Allowed Post : Call → Observable → Prop) (G : Call → Nat),
      OnTree Allowed → OnTree Post →
      (∀ c, contract? = .ok c → Shapes.Equiv stmtSem c code BumpCall) →
      (∀ c, contract? = .ok c → Shapes.Resources stmtSem c code BumpCall G) →
      ∃ c, contract? = .ok c ∧ Shapes.Certified stmtSem c code BumpCall Allowed Post G

/-- bump's postcondition: a call of `bump(a)` that succeeds leaves slot 0 holding the old `count`
plus `a`, which did not wrap and is at most `limit` (slot 1), and every other slot as it was. -/
def BumpPost (call : Call) (obs : Observable) : Prop :=
  ∃ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 ∧ call = bumpCall σ a ∧
    (obs.success = true →
      obs.storage 0 = slotValue σ 0 + a ∧ slotValue σ 0 + a ≤ slotValue σ 1 ∧
        ∀ k, k % Generic.wordSize ≠ 0 → obs.storage k = slotValue σ k)

/-- **The Statement's source half**: termination on every valid call and bump's postcondition of
every result, on the Statement's own source semantics, program and valid calls. -/
def StatementSourceHalf : Prop :=
  ∃ c, contract? = .ok c ∧ Shapes.Terminates stmtSem c BumpCall (fun _ _ => True) ∧
    Shapes.Meets stmtSem c BumpCall BumpPost

end Verify.LoopSource.MirLink

/-- info: Verify.LoopSource.Proof.LoopVC imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.Proof.LoopVC

/-- info: Verify.LoopSource.Proof.LoopBinding imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.Proof.LoopBinding

/-- info: Verify.LoopSource.Proof.LoopErased imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.Proof.LoopErased

/-- info: Verify.LoopSource.MirLink.Link imported: false -/
#guard_msgs in
#assert_not_imported Verify.LoopSource.MirLink.Link

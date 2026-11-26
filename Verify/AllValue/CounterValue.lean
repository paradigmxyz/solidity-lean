import Verify.LoopSource.Equiv.Counter.Resources
import Verify.LoopSource.Equiv.From.CtxGas
import Verify.ShapeCtxGasFrom
import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.Generic.LoopRun
import Verify.Generic.Expected
import Verify.LoopSource.MirLink.Statement
import Contracts.VerifyCounter.Source
import Verify.LoopSource.Equiv.CounterCtx

/-!
# Counter is non-payable from every caller, value and storage (R3)

`counter_nonpayable`: for every `ctx.Ok`, storage `σ`, argument `a < 2 ^ 256` and value
`0 < v < 2 ^ 256`, `bump(a)` with value `v` is rejected by SolidCore's runtime dispatcher from the
caller (`bumpFn` is non-payable: `FunctionDef.acceptsValue`), and the exact runtime bytes revert
to the same observable at every gas from `G0` (`evm7`'s block 0 jumps on `CALLVALUE` to block
1, `REVERT 0 0`; `forward_of_checkXLFrom` with the checker's `check_ok` at two blocks).
`bumpCallV σ a 0 = bumpCall σ a` (`bumpCallV_zero`), so value 0 is the existing statements' call.
-/
namespace Verify.AllValue.CounterValue
open SolarTV SolarTV.Machine SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Solar Contracts.VerifyCounter.Source SolidCore.Verify.Generic
open SolarTV.Milestone.W1

/-- `bump(a)` with call value `v` from storage `σ`: `MirLink.bumpCall` with the value free. -/
def bumpCallV (σ : List (Nat × Nat)) (a v : Nat) : Call :=
  { calldata := Abi.calldata bumpSel [a], callvalue := v, storage := σ }

/-- The gas bound of the two-block revert path: the loop checker's bound at two blocks. -/
abbrev G0 : Nat := AssembleLoop.gasBoundL Verify.LoopSource.Equiv.From.CtxGas.cx.base 2

/-- **R3, Counter is non-payable from every caller, value and storage.** For the checked
contract, every context `ctx.Ok` (caller below `2 ^ 160`, not the contract), every storage `σ`,
every argument `a < 2 ^ 256` and every call value `0 < v < 2 ^ 256`: SolidCore's runtime
dispatcher from `ctx.caller` at the statement's fuel rejects `bump(a)` (failure, no output, no
logs, storage `σ`), and EthLib runs the exact runtime bytes from `ctx.caller` to that same
observable at every gas from `G0` on. Gas is EthLib's message gas, a `Nat` with no upper bound. -/
def Statement : Prop :=
  ∀ c, contract? = .ok c → ∀ ctx : Context, ctx.Ok →
    ∀ (σ : List (Nat × Nat)) (a v : Nat), a < 2 ^ 256 → v < 2 ^ 256 → v ≠ 0 →
      Loop.runtimeRunFrom ctx.caller fuel c (bumpCallV σ a v) = some (Abi.rejected σ) ∧
        ∀ gas, G0 ≤ gas →
          runAt ctx gas (runtimeCode SolarTV.Export.Counter.bytecode) (bumpCallV σ a v) =
            some (Abi.rejected σ)

theorem bumpCallV_zero (σ : List (Nat × Nat)) (a : Nat) :
    bumpCallV σ a 0 = Verify.LoopSource.MirLink.bumpCall σ a := rfl

/-! ## The source side -/

theorem source_rejects {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (x : Nat)
    (σ : List (Nat × Nat)) {a v : Nat} (ha : a < 2 ^ 256) (hv : v < 2 ^ 256) (hv0 : v ≠ 0) :
    Loop.runtimeRunFrom x fuel c (bumpCallV σ a v) = some (Abi.rejected σ) := by
  have hfind := (Contracts.VerifyCounter.Source.shape_of hc).2.2
  have hw : widthsOf bumpFn.params bumpFn.paramAbiCleanups = some [256] := rfl
  have hargs : ∀ v ∈ [a], v < 2 ^ 256 := by simpa using ha
  have hdec : Source.ABI.decodeFunctionArgs? bumpFn (Dirty.argBytes [a]) = .ok ([a].map .word) ∨
      Source.ABI.decodeFunctionArgs? bumpFn (Dirty.argBytes [a]) = .error .empty := by
    rw [decode_args hw [a] rfl hargs]
    by_cases hclean : argsClean [256] [a] = true
    · exact Or.inl (by simp [hclean])
    · exact Or.inr (by simp [hclean])
  have hvm : v % SolidCore.Solidity.Shared.wordModulus = v := Nat.mod_eq_of_lt hv
  have hpay : bumpFn.payable = false := rfl
  have hacc : bumpFn.acceptsValue v = false := by
    simp [Source.FunctionDef.acceptsValue, hpay, Source.wordEq, SolidCore.Solidity.Shared.norm, hvm, hv0]
  have hsel : bumpSel < 2 ^ 32 := by decide
  simp only [Loop.runtimeRunFrom, Loop.runtimeResultFrom?, bumpCallV,
    Source.ABI.Contract.callCalldataAtFromWithContext?, Dirty.bytes_calldata,
    Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((EthLib.Base.natToBytes 4 bumpSel).map (·.toNat) ++ Dirty.argBytes [a]).drop
      Source.ABI.selectorBytes = Dirty.argBytes [a] by simp [Source.ABI.selectorBytes, EthLib.Base.natToBytes_length]]
  rcases hdec with hdec | hdec <;> rw [hdec] <;>
    simp only [hacc, Bool.false_eq_true, ↓reduceIte, Source.ABI.Contract.rejectedValueCall?,
      Source.ABI.Contract.revertedEmptyCall?, Source.ABI.Contract.revertedCall?,
      Source.ABI.Contract.encodeRevertData?, bind, Option.bind, Option.map_some, Source.observe,
      Abi.rejected]

/-! ## The bytecode side -/

set_option maxHeartbeats 4000000 in
theorem b0_value (o : Oracle) (call : Call) (hv : BitVec.ofNat 256 call.callvalue ≠ 0) :
    EVM.Program.block o call SolarTV.Export.Counter.evm7 (0, [], State.initial call) =
      some (.inr (1, [], State.mk Mem.initial (State.initial call).storage
        (State.initial call).transient (State.initial call).world)) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  sym_norm
  simp
  rfl

set_option maxHeartbeats 4000000 in
theorem b1_revert (o : Oracle) (call : Call) :
    EVM.Program.block o call SolarTV.Export.Counter.evm7 (1, [], State.mk Mem.initial
      (State.initial call).storage (State.initial call).transient (State.initial call).world) =
      some (.inl (.revert [], State.mk (Mem.initial.expand 0 0) (State.initial call).storage
        (State.initial call).transient (State.initial call).world)) := by
  sym_exec

theorem hit_value (o : Oracle) (call : Call) (hv : BitVec.ofNat 256 call.callvalue ≠ 0) :
    ∃ s, iterate (EVM.Program.block o call (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
      (AssembleCtx.norm SolarTV.Export.Counter.evm7))) 2 (0, [], State.initial call) =
        some (.revert [], s) := by
  refine ⟨State.mk (Mem.initial.expand 0 0) (State.initial call).storage
    (State.initial call).transient (State.initial call).world, ?_⟩
  show EVM.Program.run o _ call 2 = _
  rw [Verify.LoopSource.Equiv.CounterCtx.run_guard]
  unfold EVM.Program.run
  rw [iterate_inr (b0_value o call hv)]
  exact iterate_inl (b1_revert o call)

theorem bytes_reject {σ : List (Nat × Nat)} {a v : Nat} (hv : v < 2 ^ 256) (hv0 : v ≠ 0)
    (ctx : Context) (hctx : ctx.Ok) {gas : Nat} (hg : G0 ≤ gas) :
    runAt ctx gas (runtimeCode SolarTV.Export.Counter.bytecode) (bumpCallV σ a v) =
      some (Abi.rejected σ) := by
  have hbv : BitVec.ofNat 256 (bumpCallV σ a v).callvalue ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp [bumpCallV] at this
    exact hv0 (by omega)
  obtain ⟨s, hs⟩ := hit_value (SolidCore.Refinement.Shapes.oracleFrom ctx.caller) _ hbv
  have h := AssembleCtxGas.forward_of_checkXLFrom Verify.LoopSource.Equiv.From.CtxGas.check_ok ctx.caller
    (Assemble.address_ne_self hctx.1 hctx.2) _ (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) _ 2 _ hs hg
  show Final.Target.runWithFrom ctx.caller gas Verify.LoopSource.Equiv.From.CtxGas.code _ = _
  rw [h]
  rfl

/-- **R3.** -/
theorem counter_nonpayable : Statement := by
  intro c hc ctx hctx σ a v ha hv hv0
  exact ⟨source_rejects hc ctx.caller σ ha hv hv0, fun gas hg => bytes_reject hv hv0 ctx hctx hg⟩

example : Statement := counter_nonpayable

/-- info: 'Verify.AllValue.CounterValue.counter_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counter_nonpayable

end Verify.AllValue.CounterValue

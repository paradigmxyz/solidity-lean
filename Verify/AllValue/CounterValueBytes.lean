import Verify.LoopSource.Equiv.Counter.Resources
import Verify.LoopSource.Equiv.From.CtxGas
import Verify.ShapeCtxGasFrom
import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.Generic.LoopRun
import Verify.Generic.Expected
import Verify.LoopSource.MirLink.Statement
import Contracts.VerifyCounter.Source
import SolidCore.Refinement.Generic.StageFromValue

/-!
# Counter's bytes refuse a nonzero value on every call

The bytes side of the non-payable check, for every call rather than one selector.
`bytes_value_rejected`: for every context `ctx.Ok`, every call (any calldata, any storage) whose
value is nonzero as a word, and every gas from `G0` on, EthLib runs Counter's exact runtime bytes
from `ctx.caller` to `Abi.rejected call.storage`: failure, no output, no logs, the call's storage.
Block 0 of `evm7` jumps on `CALLVALUE` to block 1, `REVERT 0 0`, before reading any calldata
(`b0_value`, `b1_revert`), and `forward_of_checkXLFrom` carries the two-block run to the bytes
with the checker's `check_ok`.

`value_rejected_both` puts it beside the generic source side
(`SolidCore.Refinement.Generic.runFromArgs_value_inert`): when the calldata selects a function
that is not payable, the source run (if any) and the bytes agree on failure, no logs and the
call's storage.
-/
namespace Verify.AllValue.CounterValueBytes
open SolarTV SolarTV.Machine SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Solar SolidCore.Verify.Generic

/-- The gas bound of the two-block revert path: the loop checker's bound at two blocks. -/
abbrev G0 : Nat := AssembleLoop.gasBoundL Verify.LoopSource.Equiv.From.CtxGas.cx.base 2

/-- **The generic guard.** In any EVM IR program, a block that opens with `CALLVALUE; JUMPI t`
jumps to `t` on a nonzero value, with the stack and state it started from, whatever follows. -/
theorem block_callvalue_guard (o : Oracle) (call : Call) (p : EVM.Program.Program) {b t : Nat}
    {rest : List EVM.Program.Instr}
    (hb : p.blocks[b]? = some (.effect .callvalue 0 :: .jumpi t :: rest)) (s : State)
    (hv : BitVec.ofNat 256 call.callvalue ≠ 0) :
    EVM.Program.block o call p (b, [], s) = some (.inr (t, [], s)) := by
  simp only [EVM.Program.block, hb, EVM.Program.exec, Effect.apply]
  simp only [List.length_nil, List.take_zero, List.drop_zero, List.length_cons, Nat.lt_irrefl,
    ↓reduceIte, hv]
  simp

/-- Block 0 of Counter's program is that guard: it jumps to block 1 on a nonzero `CALLVALUE`,
whatever the calldata and storage. -/
theorem b0_value (o : Oracle) (call : Call) (hv : BitVec.ofNat 256 call.callvalue ≠ 0) :
    EVM.Program.block o call SolarTV.Export.Counter.evm7 (0, [], State.initial call) =
      some (.inr (1, [], State.mk Mem.initial (State.initial call).storage
        (State.initial call).transient (State.initial call).world)) :=
  block_callvalue_guard o call _ rfl _ hv

/-- In any EVM IR program, a block `PUSH 0; PUSH 0; REVERT` from an empty stack reverts with no
data. -/
theorem block_revert_empty (o : Oracle) (call : Call) (p : EVM.Program.Program) {b : Nat}
    (hb : p.blocks[b]? = some [.op (.stack (.push 0)), .op (.stack (.push 0)), .revert]) (s : State) :
    EVM.Program.block o call p (b, [], s) =
      some (.inl (.revert [], { s with memory := s.memory.expand 0 0 })) := by
  simp only [EVM.Program.block, hb, EVM.Program.exec, EVM.Program.stepOp]
  rfl

/-- Block 1 of Counter's program is `REVERT 0 0`. -/
theorem b1_revert (o : Oracle) (call : Call) :
    EVM.Program.block o call SolarTV.Export.Counter.evm7 (1, [], State.mk Mem.initial
      (State.initial call).storage (State.initial call).transient (State.initial call).world) =
      some (.inl (.revert [], State.mk (Mem.initial.expand 0 0) (State.initial call).storage
        (State.initial call).transient (State.initial call).world)) :=
  block_revert_empty o call _ rfl _

theorem guard_nil (p : Assemble.Program) : AssembleCtxGas.guard [] p = p := by
  cases p with
  | mk blocks =>
    simp only [AssembleCtxGas.guard, List.contains_nil, Bool.false_eq_true, ↓reduceIte]
    congr 1
    induction blocks with
    | nil => rfl
    | cons b bs ih => simp [List.mapIdx_cons, ih]

/-- The checked program reverts with no data in two blocks on a nonzero value. -/
theorem hit_value (o : Oracle) (call : Call) (hv : BitVec.ofNat 256 call.callvalue ≠ 0) :
    ∃ s, iterate (EVM.Program.block o call (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
      (AssembleCtx.norm SolarTV.Export.Counter.evm7))) 2 (0, [], State.initial call) =
        some (.revert [], s) := by
  refine ⟨State.mk (Mem.initial.expand 0 0) (State.initial call).storage
    (State.initial call).transient (State.initial call).world, ?_⟩
  have h := congrFun (congrFun (AssembleCtx.run_norm o SolarTV.Export.Counter.evm7) call) 2
  show EVM.Program.run o (AssembleCtxGas.guard [] _) call 2 = _
  rw [guard_nil, h]
  unfold EVM.Program.run
  rw [iterate_inr (b0_value o call hv)]
  exact iterate_inl (b1_revert o call)

/-- A value that is nonzero as a word is a nonzero `CALLVALUE`. -/
theorem callvalue_ne {call : Call} (hv : SolidCore.Solidity.Shared.norm call.callvalue ≠ 0) :
    BitVec.ofNat 256 call.callvalue ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  exact hv this

/-- **The bytes side.** Counter's exact runtime bytes, run by EthLib from any `ctx.Ok` at any gas
from `G0`, reject every call that carries a nonzero value: any calldata, any storage. -/
theorem bytes_value_rejected (ctx : Context) (hctx : ctx.Ok) (call : Call)
    (hv : SolidCore.Solidity.Shared.norm call.callvalue ≠ 0) {gas : Nat} (hg : G0 ≤ gas) :
    runAt ctx gas (runtimeCode SolarTV.Export.Counter.bytecode) call =
      some (Abi.rejected call.storage) := by
  obtain ⟨s, hs⟩ := hit_value (SolidCore.Refinement.Shapes.oracleFrom ctx.caller) call (callvalue_ne hv)
  have h := AssembleCtxGas.forward_of_checkXLFrom Verify.LoopSource.Equiv.From.CtxGas.check_ok ctx.caller
    (Assemble.address_ne_self hctx.1 hctx.2) _ (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) _ 2 _ hs hg
  show Final.Target.runWithFrom ctx.caller gas Verify.LoopSource.Equiv.From.CtxGas.code _ = _
  rw [h]
  rfl

/-- **Both sides.** When the calldata selects a function that is not payable and the value is
nonzero as a word: SolidCore's run against any contract deployed with any argument words, if it
ends, fails with no logs and the call's storage, and Counter's bytes end in exactly that, with no
output, at every gas from `G0`. -/
theorem value_rejected_both {fuel : Nat} {ws : List Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (ctx : Context) (hctx : ctx.Ok) (call : Call) {sel : Nat} {f : SolidCore.Solidity.Source.FunctionDef}
    (hsel : SolidCore.Solidity.Source.ABI.readSelector? (callBytes call) = some sel)
    (hf : c.core.findFunctionBySelector? sel = some f) (hpay : f.payable = false)
    (hv : SolidCore.Solidity.Shared.norm call.callvalue ≠ 0) :
    (∀ obs : Observable, SolidCore.Refinement.Source.runFromArgs ctx.caller fuel ws c call = some obs →
      obs.success = (Abi.rejected call.storage).success ∧ obs.logs = (Abi.rejected call.storage).logs ∧
        obs.storage = (Abi.rejected call.storage).storage) ∧
      ∀ gas, G0 ≤ gas →
        runAt ctx gas (runtimeCode SolarTV.Export.Counter.bytecode) call =
          some (Abi.rejected call.storage) :=
  ⟨fun _ hrun => runFromArgs_value_inert hsel hf hpay hv hrun,
    fun _ hg => bytes_value_rejected ctx hctx call hv hg⟩

/-- info: 'Verify.AllValue.CounterValueBytes.value_rejected_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms value_rejected_both

end Verify.AllValue.CounterValueBytes

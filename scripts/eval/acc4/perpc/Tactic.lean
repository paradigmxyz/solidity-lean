import PerPC.Entry

/-! Bench only: sym_exec with block-entry equations (PerPC.Entry). Every other step is
sym_exec own, copied from W1Proofs.Tactic. -/

namespace SolarTV.Milestone.W1
open EvmRules Machine SolarTV.Eval.PerPC

macro "sym_eval_pc" : tactic => `(tactic|
  dsimp only [↓blockEntry, iterate_mk, iterate_zero, listLookup, listLength, moduleEntry, functionParams,
    foldNot, foldShl, foldShr, foldAdd, foldSub, foldMul, foldAnd, foldOr, foldXor, foldLt, foldGt,
    foldEq, tableEntry,
    MIR.Lowered.Module.run, MIR.Lowered.moduleBlock, MIR.Lowered.segment,
    MIR.Lowered.splitCall, MIR.Lowered.bindResult, MIR.Lowered.bindResults,
    MIR.Lowered.bindExtras, MIR.Lowered.publishResults, MIR.Lowered.publishWords, MIR.Lowered.bindPhis,
    MIR.Lowered.bindParams, MIR.Lowered.execInsts, MIR.Lowered.Operand.eval,
    MIR.Lowered.Env.set, MIR.Lowered.switchTarget, MIR.Lowered.halt, MIR.Lowered.evalPure,
    MIR.Lowered.lowBits, MIR.Lowered.selectWord, MIR.Lowered.Function.start,
    MIR.Lowered.Module.startState, List.find?_cons, List.find?_nil, Nat.reduceBEq,
    EVM.Program.run, EVM.Program.block, EVM.Program.exec, EVM.Program.stepOp,
    EVM.Program.output, EVM.Program.context, EVM.stepChecked,
    step_add, step_mul, step_and, step_or, step_xor, step_div, step_sdiv, step_mod, step_smod,
    step_signextend, step_byte, step_shl, step_shr, step_sar, step_lt, step_gt, step_slt, step_sgt,
    step_eq, step_sub, step_exp, step_addmod, step_mulmod, step_not, step_clz, step_iszero,
    step_pop, step_dup, step_swap, step_calldatasize, step_returndatasize, step_push, apply_mload,
    apply_mstore, apply_mstore8, apply_msize, apply_sload, apply_sstore, apply_tload,
    apply_tstore, apply_calldatasize, apply_callvalue, apply_caller, apply_address,
    apply_returndatasize, apply_keccak256, apply_log0, apply_log1, apply_log2, apply_log3,
    apply_log4, logged, apply_gas, apply_immutable, ImmutableRead.apply, apply_codecopy, apply_create,
    apply_create2, created, apply_env, apply_calldatacopy, apply_mcopy,
    apply_returndatacopy, apply_call, apply_callcode, apply_delegatecall,
    apply_staticcall, called, returndataSize, BitVec.reduceToNat,
    List.map, List.take, List.drop, List.set, List.length, List.find?, Nat.reduceBEq,
    Except.map, Option.map,
    Option.isSome, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, evmNotLit, finValue])

macro "sym_norm_pc" : tactic => `(tactic| repeat (first | sym_eval_pc | sym_cond | sym_mem))

set_option hygiene false in
macro "sym_exec_pc" : tactic => `(tactic| (
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  sym_norm_pc
  repeat' ((first | split_cond | split_table) <;> sym_norm_pc)
  all_goals first
    | with_reducible rfl
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)
    | (exfalso; sym_comm_contra)
    | sym_select
    | sym_agree
    | sym_expand
    | (sym_mem_order <;> first
        | with_reducible rfl
        | (exfalso; bv_omega)
        | (exfalso; sym_omega)
        | (exfalso; sym_comm_contra)
        | sym_select
        | sym_agree)
    | fail "sym_exec: the runs end in different results on this path, or the procedure cannot tell"))

end SolarTV.Milestone.W1

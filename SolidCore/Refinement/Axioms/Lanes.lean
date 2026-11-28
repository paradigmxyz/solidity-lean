import SolidCore.Refinement.Axioms.Audit
import SolidCore.Refinement.Generic.CallNode
import SolidCore.Refinement.Generic.Loop
import SolidCore.Refinement.Generic.LoopErr
import SolidCore.Refinement.Generic.LoopRun
import SolidCore.Refinement.Generic.LoopSeq
import SolidCore.Refinement.Generic.LoopStmt
import SolidCore.Refinement.Generic.MirNoLog
import SolidCore.Refinement.Solar.AssembleCallValue
import SolidCore.Refinement.Solar.AssembleCallValueEffect
import SolidCore.Refinement.Solar.AssembleCallValueZero
import SolidCore.Refinement.Solar.AssembleCodeCopy
import SolidCore.Refinement.Solar.AssembleCreate
import SolidCore.Refinement.Solar.AssembleCreateBack
import SolidCore.Refinement.Solar.AssembleCtx
import SolidCore.Refinement.Solar.AssembleCtxExample
import SolidCore.Refinement.Solar.AssembleCtxTrack
import SolidCore.Refinement.Solar.AssembleCtxCall
import SolidCore.Refinement.Solar.AssembleRevert
import SolidCore.Refinement.Solar.AssembleRevertCall
import SolidCore.Refinement.Solar.AssembleRevertCut
import SolidCore.Refinement.Solar.AssembleRevertCutExample
import SolidCore.Refinement.Solar.AssembleRevertExample
import SolidCore.Refinement.Solar.EthLibErr
import SolidCore.Refinement.Solar.EthLibErrLow
import SolidCore.Refinement.Solar.AssembleCreateExample
import SolidCore.Refinement.Solar.AssembleCreateCut
import SolidCore.Refinement.Solar.AssembleCreateRun
import SolidCore.Refinement.Solar.AssembleCallValueSeg
import SolidCore.Refinement.Solar.AssembleCallValueZeroSeg
import SolidCore.Refinement.Solar.AssembleCreateSeg
import SolidCore.Refinement.Solar.AssembleCreateSegOracle
import SolidCore.Refinement.Solar.AssembleCreateCutQ
import SolidCore.Refinement.Solar.AssembleCreateSegF
import SolidCore.Refinement.Solar.AssembleCreateRunF
import SolidCore.Solidity.StagedK
import SolidCore.Solidity.StagedL

/-! Axiom pass for the reusable lane theorems: source loops with ranking certificates and their
error paths (`Generic/Loop*`), the low-level call node (`Generic/CallNode`), MIR runs without
logs (`Generic/MirNoLog`), the context-sensitive checker (`AssembleCtx*`), revert data
(`AssembleRevert*`, `EthLibErr*`), and CODECOPY, CREATE2 and CALL with value
(`AssembleCodeCopy`, `AssembleCreate*`, `AssembleCallValue*`). Every `#print axioms` below must
report a subset of [propext, Classical.choice, Quot.sound], and the sweep must report no
violation. Run with `scripts/refinement/axiom-audit.sh`. -/

-- Source loops: ranking certificates, termination and the error paths.
#print axioms SolidCore.Refinement.Generic.Loop.forLoop_of_cert
#print axioms SolidCore.Refinement.Generic.Loop.forLoop_never
#print axioms SolidCore.Refinement.Generic.Loop.forLoop_err
#print axioms SolidCore.Refinement.Generic.Loop.runtime_run_err
#print axioms SolidCore.Refinement.Generic.Loop.runtime_run_clean
#print axioms SolidCore.Refinement.Generic.Loop.eval_incField
#print axioms SolidCore.Refinement.Generic.Loop.eval_incVar

-- Source call node and MIR without logs.
#print axioms SolidCore.Refinement.CallNode.eval_lowLevelCall
#print axioms SolarTV.MIR.Lowered.Module.ends_logs

-- Context-sensitive checker.
#print axioms SolidCore.Refinement.Solar.AssembleCtx.withinRun_of_checkX
#print axioms SolidCore.Refinement.Solar.AssembleCtx.assembly_of_checkX
#print axioms SolidCore.Refinement.Solar.AssembleCtx.withinRun_mir_of_checkX
#print axioms SolidCore.Refinement.Solar.AssembleCtxExample.bytecode
#print axioms SolidCore.Refinement.Solar.AssembleCtx.assembly_of_checkXB
#print axioms SolidCore.Refinement.Solar.AssembleCtx.assembly_of_checkXB_norm

-- Revert data.
#print axioms EthLib.Execution.Evm.RevertErr.step_good
#print axioms EthLib.Execution.Evm.RevertErr.SpecG.lowE
#print axioms SolidCore.Refinement.Solar.AssembleLoop.withinR_of_checkL
#print axioms SolidCore.Refinement.Solar.AssembleRevertCut.withinRunR_of_checkC
#print axioms SolidCore.Refinement.Solar.AssembleRevertCut.withinRunR_mir_of_checkC
#print axioms SolidCore.Refinement.Solar.AssembleRevertCall.runs_of_checkCBR
#print axioms SolidCore.Refinement.Solar.AssembleRevertExample.bytecode
#print axioms SolidCore.Refinement.Solar.AssembleRevertExample.mutant_fails
#print axioms SolidCore.Refinement.Solar.AssembleRevertCutExample.bytecode

-- CODECOPY, CREATE2 and CALL with value.
#print axioms SolidCore.Refinement.Solar.AssembleCodeCopy.codecopy_dyn
#print axioms SolidCore.Refinement.Solar.AssembleCodeCopy.codeOracle_ok
#print axioms SolidCore.Refinement.Solar.AssembleCreate.create2Address_toU256
#print axioms SolidCore.Refinement.Solar.AssembleCreateBack.create2_back
#print axioms SolidCore.Refinement.Solar.AssembleCallValue.callValue_back
#print axioms SolidCore.Refinement.Solar.AssembleCallValueZero.call0_back
#print axioms SolidCore.Refinement.Solar.AssembleCallValueEffect.call_effectW
#print axioms SolidCore.Refinement.Solar.AssembleCallValueEffect.create2_effectW

-- CREATE2, CALL and CODECOPY as cuts of a run, and their run oracle.
#print axioms SolidCore.Refinement.Solar.AssembleCreateSeg.create2_cut
#print axioms SolidCore.Refinement.Solar.AssembleCreateSeg.create2_apply
#print axioms SolidCore.Refinement.Solar.AssembleCreateSeg.codecopy_cut
#print axioms SolidCore.Refinement.Solar.AssembleCallValueSeg.callValue_cut
#print axioms SolidCore.Refinement.Solar.AssembleCallValueZeroSeg.call0_cut
#print axioms SolidCore.Refinement.Solar.AssembleCreateSegOracle.apply_call_createOracle
#print axioms SolidCore.Refinement.Solar.AssembleCreateSegOracle.rdRel_read

-- The checker cut at CALL, CREATE2 and CODECOPY, and runs with creations.
#print axioms SolidCore.Refinement.Solar.AssembleLoop.exec_simC
#print axioms SolidCore.Refinement.Solar.AssembleCreateCut.exec_codecopy
#print axioms SolidCore.Refinement.Solar.AssembleCreateRun.exec_F
#print axioms SolidCore.Refinement.Solar.AssembleCreateRun.FO_ok
#print axioms SolidCore.Refinement.Solar.AssembleCreateRun.exec_gasF
#print axioms SolidCore.Refinement.Solar.AssembleCreateRun.create2_table
#print axioms SolidCore.Refinement.Solar.AssembleCreateExample.check_ok
#print axioms SolidCore.Refinement.Solar.AssembleCreateExample.mutantSalt_fails
#print axioms SolidCore.Refinement.Solar.AssembleCreateExample.nocreates_fails

-- Staged source-translation checks: kernel-cheap equal forms and the lemmas that assemble a
-- contract's translation from its separately checked context, function groups and assembly.
#print axioms SolidCore.Solidity.Executable.TypeEnv.shadowedStateNames_eq_K
#print axioms SolidCore.Solidity.Executable.stringDecEq_eq_K
#print axioms SolidCore.Solidity.Executable.toByteArray_eq_K
#print axioms SolidCore.Solidity.Executable.ContractDecl.toCoreFromOrders?_of_stages
#print axioms SolidCore.Solidity.Executable.FromOrdersCtx.group?_of_pairs
#print axioms SolidCore.Solidity.Executable.FunctionDecl.toCore_eq_staged
#print axioms SolidCore.Solidity.Executable.FromOrdersCtx.pairF_of_stages

-- CALL and CREATE2 with callee frames pinned to the caller state, read segments over the run
-- oracle with creations, and the checker's runs with calls and creations (checkCF).
#print axioms SolidCore.Refinement.Solar.AssembleCreateCutQ.call0_cutQ
#print axioms SolidCore.Refinement.Solar.AssembleCreateCutQ.callValue_cutQ
#print axioms SolidCore.Refinement.Solar.AssembleCreateCutQ.create2_cutQ
#print axioms SolidCore.Refinement.Solar.AssembleCreateSegF.segF
#print axioms SolidCore.Refinement.Solar.AssembleCreateRunF.runs_of_checkCF
#print axioms SolidCore.Refinement.Solar.AssembleCreateRunF.withinRun_of_checkCF
#print axioms SolidCore.Refinement.Solar.AssembleCreateRunF.assembly_of_checkCF
#print axioms SolidCore.Refinement.Solar.AssembleCreateRunF.withinRun_mir_of_checkCF
#print axioms SolidCore.Refinement.Solar.AssembleCreateRunF.holds_of_checkCF
#print axioms SolidCore.Refinement.Solar.AssembleCreateRunF.example_runs
#print axioms SolidCore.Refinement.Solar.AssembleCreateRunF.example_mutants

#axiom_audit ".lake/axiom-closure-lanes.txt" "SolidCore.Refinement.Solar" "SolidCore.Refinement.Generic" "SolarTV" "SolidCore.Solidity.Staged"

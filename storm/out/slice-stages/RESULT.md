# slice-stages: UniswapV2ERC20.transfer backend stages in CI

Base: solidity-lean 9fb89ee (alpharush/certified-translation). Solar base 7b6afda8.

## What is proved, with receipts

**Stage0 (source MIR) → evm11 (final EVM IR), scoped to calls of transfer(address,uint256), both directions**, generated from the release solar binary and checked by the new CI step:

- \`SolarTV.Milestone.Uv2Erc20T.uv2_erc20_transfer_mir_to_evmir (o : Oracle) : Stage (mirSem o) (evmirSem o) stage0 evm11 scope\`
- \`uv2_erc20_transfer_certified\`, \`uv2_erc20_transfer_certified_back\`
- each \`#print axioms\` pinned by \`#guard_msgs\` to [propext, Classical.choice, Quot.sound].
- Stages: stage0, mir1..mir4, sched, evm1..evm11 (the passes that changed the code under \`-Ogas --evm-version osaka\`, release build).
- \`ProofsT/Assembly\`: the exact runtime bytes (1183) decode to the item stream of evm11 (\`walk_sound\`), kernel-checked.
- \`Ctx.check_ok : checkXB prog code cx = true\` (checker with contexts accepts the exact bytes against evm11), axioms [propext, Classical.choice, Quot.sound].
- No \`sorry\`, \`native_decide\`, \`bv_decide\` or \`axiom\` anywhere in Generated/ (grep).

Receipts (hosted Linux, LEAN_NUM_THREADS=2, max RSS = largest single process):

| command | exit | wall | peak |
|---|---|---|---|
| \`scripts/verify/uniswap_v2_stages.sh\` (SOLAR_DIR = solar at 628e5dcb, release binary prebuilt) | 0 | <1 s | 17 MB |
| \`lake build -KleanMemory=6000 uv2_erc20\` (clean Generated/, 2668 jobs) | 0 | 194 s | 4693 MB (uv2_erc20.Ctx; per-module VmHWM: Ctx 4.80 GB, CtxNeg 3.26 GB, AssembleNoCall 2.31 GB, Runs.Evm2 2.09 GB, Runs.Sched 2.07 GB) |
| same, after the negative control was restored | 0 | 23 s | 1885 MB |
| \`lake build -KleanMemory=3000 EvmRules SolarTV W1Proofs W1 counter w4 masks bank c4 mulx events reader verify_token verify_counter callsqrt arraymax\` (every existing target that imports the changed tv/W1Proofs/Segment.lean) | 0 | 2188 s | 4208 MB |

Logs: \`ci.log\`, \`rebuild.log\`, \`certified.log\`, \`neg_stage.log\`.

## Negative controls (refused by execution)

- Stage: swapping \`.sub\`/\`.add\` in evm11 (4 sites) and rebuilding \`uv2_erc20.ProofsT.Runs.Evm11\`: exit 1, 77 s, 2293 MB; 7 errors \`sym_seg: the segments end differently on this path\` (symbolic execution reaching different ends), plus 1 heartbeat timeout on another goal. Restored and rebuilt: exit 0.
- Bytes: \`CtxNeg\` builds \`rejects_jump\` (pushed jump target moved), \`rejects_sstore\` (SSTORE → POP), \`rejects_opcode\` (SSTORE → CREATE): each \`checkXB prog (mutant i b) cx = false := by decide +kernel\`.

## Not proved (not labelled stronger)

- **EVM IR → exact bytes (E5) is blocked for this contract.** The runtime bytes are not call-free (STATICCALL at pc 903 from permit's ecrecover; RETURNDATASIZE/RETURNDATACOPY at 1158–1162), so \`AssembleNoCall.assembly_of_checkXB_norm_callFree\` does not apply, and the checker's per-run theorem would rest on \`StaticRunner\`, which AssembleNoCall refutes. Ctx.lean states \`not_call_free : AssembleNoCall.callFree code = false\` and **no bytes theorem**. Closing it needs a scoped/reachability argument (transfer's path never reaches the call) or a sound runner for calls.
- No source → MIR (E0/E1) or spec claims here.

## Changes

solidity-lean (\`solidity-lean-patches/\`, \`solidity-lean.bundle\` = 9fb89ee..61c33d6):

1. \`fix(tv): fold right literals of || and && by rewriting\`: \`boolLit\`/\`boolAndLit\` folded \`b || true\` as a dsimp step, which is not definitional while \`b\` is unknown, so the kernel refused the term; right literals now go through \`Bool.or_true\` etc. in \`seg_cut_test\`, plus \`ite_or_ite_not\`. All existing Segment users rebuilt (table above).
2. \`feat(verify): UniswapV2ERC20.transfer backend stages\`: \`scripts/verify/uniswap_v2_stages.sh\` (compiles the port with solar at the pinned commit, generates the transfer-scoped stage proofs with \`--cut --joins --no-mir-joins --segment 8\` and 12 non-transfer selectors excluded, and the bytes certificate; the last stage file is read from the manifest), pin \`scripts/verify/uniswap_v2_stages-solar-rev\`, lean_lib \`uv2_erc20\` (srcDir Generated, -M 6000, roots ProofsT.Stages, ProofsT.Assembly, Ctx, CtxNeg), Generated/ ignored (GPL port never committed), and the refinement.yml step after the port generation.

solar (\`solar-patches/\`, \`solar.bundle\` = 7b6afda8..628e5dcb, branch slice/stages): fixed statements and clean replay; open-world statement kind; scoped stage proofs cut block by block (\`--cut/--joins/--segment/--no-mir-joins/--exclude\`); asm_ctx.py checker-with-contexts certificate; bytes theorem only for call-free code (else \`not_call_free\` + CtxNeg).

## Before CI can pass

- **Pin not on GitHub:** \`uniswap_v2_stages-solar-rev\` = 628e5dcb3bc15cc3d7a96437f7ffa4eed488bab1 exists only in \`solar.bundle\`. The CI step fetches it from paradigmxyz/solar and fails until these commits are relayed there (then re-pin to the landed SHA).
- **Build profile changes the bytes:** a debug solar build defaults \`-Zcheck-analyses\` on (\`lower_assumes.rs: should_check_analyses\`), adding lower-assumes, tail-merge and loop-layout stages (stage0..evm16) and different bytes. The script builds and uses the release binary; proofs here are for the release output. Earlier evm16 results in this lane were from a debug build and are superseded.

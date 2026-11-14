# memory-patterns: result

Base: solidity-lean `9fb89ee` (rebased from `a1c3143`, no conflicts). solar base `38b5232ad` (alpharush/certified).

- `memory-patterns.bundle`: `git fetch memory-patterns.bundle mem/v2` gives 9 commits on `9fb89ee` (head `9f045e45`).
- `solar-memory-patterns.bundle`: 1 commit on solar `38b5232ad` (head `6aaf60b26`): `tools/certify/asm_cert.py` follows the new loop-checker semantics.
- `logs/`: the two driver runs and the regression build.

## Checked pattern contracts

| contract | pattern | driver (scripts/certify) | published gas |
|---|---|---|---|
| `abi_hash` (`hashPair(uint256,uint256) returns uint256(keccak256(abi.encode(a,b)))`) | ABI encode of two words into scratch memory, keccak, return | **CHECKED**, EXIT 0, `Certified.abi_hash.Final.final`, 23 stage theorems audited, kernel replay of 423 modules ([log](logs/certify-abi_hash.log)) | 10000000 |
| `event_words` (Swap-shaped event: 2 indexed topics, 4 data words written at the free memory pointer 0x80) | heap writes via free-memory pointer + LOG3 from heap | **CHECKED**, EXIT 0, `Certified.event_words.Final.final`, 47 stage theorems audited, kernel replay of 439 modules ([log](logs/certify-event_words.log)) | 10210224 |

Both `check_final` lines: axioms `[propext, Classical.choice, Quot.sound]`. Both are "CHECKED, not certified: not proved: spec" (no end-to-end spec theorem was asked of them; E3 source stage, E4 backend stages and E5 assembly are proved).

Source stage (E3) theorems, `#print axioms` all within the three axioms:
- `SolidCore.Refinement.Solar.AbiHash`: `shape_eq`, `check_stage0`, `checkValue_stage0`, `check_rejects_order/size/arg`, `lowering`, `loweringValue` (premise `Generic.SourceEnvOk o` = CallerOk + HashOk; no hash-separation premise).
- `SolidCore.Refinement.Solar.EventWords`: `selector_eq`, `digest_eq`, `shape_eq`, `check_stage0`, `checkValue_stage0`, `check_rejects_caller/topic/order/data/heap`, `lowering`, `loweringValue` (premise `Generic.CallerOk o`).

## What changed to get there

1. Generic symbolic MIR run takes the entry heap (`symStart`, `symEntryStart`), a `heap_floor` constant and `mload` at a constant offset; `MirRun` soundness re-proved.
2. `eraseExpr` handles `uint256(keccak256(abi.encode(x, y)))` of two atoms as `WExpr.hash`.
3. Loop/cut assembly checker (E5): `Known := List (Option Word)` with relation `KR` replaces the two-word stack-prefix `known`. PUSH/DUP add what they know at any depth, pop-push ops keep what lies below their inputs, MSTORE/CALLDATALOAD/CALLER keep the rest. That was the event_words E5 blocker: the 0x80 pointer was lost before the MSTOREs and LOG3. `exec_simL`/`exec_simC` re-proved; their `#guard_msgs` axiom checks pass. Every `blockOkC` client is updated (CallSeg, CreateSegF/RunF, Ctx, CtxCall, RevertCall/Cut, RunLoop, LoopRun, NoCall).
4. solar `asm_cert.py` mirrors (3), so the inferred certificate for event_words is `top := 256` (it was 128, which was wrong).

## Build receipts (rebased tree, head 9f045e45)

```
LEAN_NUM_THREADS=1 lake -R -KleanMemory=4000 build SolidCore.Refinement.Solar.AssembleNoCallExample Verify.ShapeGeneric \
  Contracts.VerifyCounter.Assembly Contracts.VerifyCounter.Shape events.Shape mulx.Shape bank.Shape \
  abi_hash.Final event_words.Final SolidCore.Refinement.Solar.AbiHash.Lowering SolidCore.Refinement.Solar.EventWords.Lowering
EXIT 0  Build completed successfully (2857 jobs)
```
Memory: per-file cap -M 4000 MB (the checker files were first built at -M 6000; AbiHash.Lowering needs -K5000 from cold). The existing certificates (bank, events, mulx, VerifyCounter) still pass: the new checker accepts everything the old one did.

The driver runs used the pre-rebase base `a1c3143` plus these commits; the rebase onto `9fb89ee` only adds AssembleNoCall/HashScope files. The regression build above rebuilt both `Final` modules on the rebased tree.

Driver command: `SOLIDITY_LEAN_DIR=<solidity-lean> CERTIFY_ALLOW_UNPINNED=1 LEAN_MEMORY=5000 scripts/certify <name>.sol` (solc 0.8.35).

## Exact blockers for the remaining patterns

| pattern (source in `scripts/refinement/mem/`) | stage | blocker |
|---|---|---|
| EventDyn (event with `bytes calldata`) | E3 `Generic.symTree`; E5 | memory only at constant offsets and sizes: `calldatacopy` with a symbolic length has no symbolic effect, and the loop checker needs constant ranges (the cut checker's `DYN_TOP` path covers E5 but not E3) |
| RetDecode / SafeTransfer / TryCatch (ABI decode of return data; Pair token calls) | E3 | `Generic.symEffect` has no call/staticcall/returndata effects and `eraseStmt` no external calls (E5 already has AssembleCut call segments) |
| Revert bubbling via inline assembly | E1 | the frontend (`solc_ast_to_lean_source.py`) refuses Yul nodes |
| Factory salt `keccak256(abi.encodePacked(address,address))` (40 bytes) | E3 | `symEffect` hashes only 64-byte two-word memory and `WExpr.hash` is two words; it needs a packed-bytes hash term |
| ArraySum / MemFmp / KeccakMem (memory arrays) | not run through the driver | sources are in place; not yet run. They are expected to hit the same E3 constant-offset limit as EventDyn wherever an offset or length is symbolic (unverified) |

For the first slice (UniswapV2ERC20.transfer), the Transfer event logs from scratch memory and needs none of these. Pair's Swap/Mint/Burn/Sync events use the heap the way event_words does, which is now checked.

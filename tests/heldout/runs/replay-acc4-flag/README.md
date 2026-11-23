# Replay negatives against acc4-flag

Positive: acc4-flag. Its record is at solidity-lean `alpharush/t1-generic-records` @ d66e60bf, under `Certified/record/acc4-flag/replay`. Its strict run exited 0, and its fresh-clone `--replay` exited 0 on driver 6d0f2621 with base 44572c15, with all 18 REPLAY_KEYS the same. That replay's receipt is at 4df9c420, under `Certified/record/acc4-flag-replay/`. These results supersede `../replay-acc3-flag/`: acc3-flag failed its own fresh-clone replay, because its `inputs_sha256` embedded an absolute source path.

Drivers are solar `alpharush/t1-generic-driver` @ 6d0f2621 (the pin layer) and `alpharush/t1-driver-on-2637b` @ 1844041e and @ 800d78a9 (the claim, input and sibling cases). Each row names its driver. None of the drivers was edited.

Methods:

- **manifest**: the driver's own `--replay` stops before any fresh run. No Lean runs.
- **one full run**: `negatives.py --replay-from` runs the driver's `--replay` end to end, including a cold fresh certify. `receipt.py` wraps it and samples a 2 s trace.
- **comparison reuse**: `reuse.py` imports the driver's `generic.py` and calls `replay_main` unchanged. The fresh-run subprocess is replaced by a copy of a fresh record and its exit code. The fresh record used is T1's published fresh run of acc4-flag (4df9c420, CERTIFIED, exit 0). This is "driver comparison reused on one fresh run": every comparison, check and message is the driver's own, but no new Lean run backs the row.

## File layer (driver 6d0f2621, manifest)

Nine cases, all REJECTED with exit 1 at the manifest: `file/table.md`, `file/log/`.

## Pin layer

| case | method | driver | exit | differing key |
|---|---|---|---|---|
| stale-source@pin | manifest | 6d0f2621 | 1 | the record's source digest is not its source file's |
| stale-bytes@pin | one full run (13808 s) | 6d0f2621 | 1 | bytecode_sha256 (record 1f1579b3…, fresh f689833e…) |
| stale-bytes@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | bytecode_sha256 |
| flipped-byte@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | bytecode_sha256 |
| changed-solar-options@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | options |
| stale-spec-hash@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | spec |
| stale-import@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | solidity_lean.inputs_sha256; on 800d78a9: solidity_lean.inputs and inputs_sha256 do not name the same generated inputs |
| omitted-selector@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | functions |
| false-env-pin@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | environment |
| oog-as-revert@pin | comparison reuse | 6d0f2621, 800d78a9 | 1, 1 | gas_bound (record 1790101, fresh 3580203) |
| unedited control | comparison reuse | 6d0f2621, 800d78a9 | 0, 0 | none: CERTIFIED, every pin reproduced |

The full run is not a clean pass. Its REJECTED names the right key, but its own fresh certify did not finish CERTIFIED. It stopped at the final-negatives stage with `REJECTED: driver: UnicodeDecodeError: 'utf-8' codec can't decode byte 0xe2 in position 195`. The bytecode had already been produced and was compared, so the right key was still named, but the fresh run's status is REJECTED (`pin/e2e/fresh-record.json`).

The cause is a driver issue that depends on the length of the work path. `final_neg.sh` cuts a Lean error line with `cut -c1-160`, which counts bytes in this environment. The sorry-proof variant's message ends in a hygienic name containing `✝` (3 bytes). With this run's longer work path, the cut fell inside that character. `generic.py` reads the script's output with `Popen(text=True)`, which raised on the invalid byte. The same line in T1's replay was shorter and did not split. `final_neg.sh` and the reader are the same at 800d78a9.

For that reason, the reuse rows use T1's CERTIFIED fresh run, not this one. Receipt: `pin/e2e/receipt.json` (exit 1, 13808.3 s wall, peak tree RSS 8799 MiB, 6901 samples), with the trace in `receipt.trace.tsv`.

## Claim, input and sibling tampers (LANE 4)

Every case edits a copy of acc4-flag's `replay/`. The scripts are in `lane4/scripts/` and the logs in `lane4/log/`. "Before" is 6d0f2621 and c09510a3, whose `replay_main` is byte-identical; the full before/after table is in `docs/MUTATIONS_GENERIC.md`.

| case | edit | method | before | 1844041e | 800d78a9 |
|---|---|---|---|---|---|
| theorem-renamed | record.json final.theorem | comparison reuse, then manifest | 0 CERTIFIED | 1 final.theorem | 1 final.theorem |
| statement-edited | final.statement | same | 0 | 1 final.statement | 1 final.statement |
| closure-altered | replay.closure and replayed_count 3966 -> 3967 | same | 0 | 1 replay.closure | 1 replay.closure |
| unaccounted-hidden | replay.replayed one module shorter | same | 0 | 1 replay.replayed | 1 replay.replayed |
| assumptions-dropped | final.excluded = [] | same | 0 | 1 final.excluded | 1 final.excluded |
| caveats-dropped | caveats = [] in record.json only | manifest | – | 1 caveats | 1 caveats |
| strict-forged | strict.components.spec = false | manifest | – | 1 strict.components.spec | 1 strict.components.spec |
| forged-consistent | theorem edited in both records, run_files rehashed | comparison reuse | – | 1 final.theorem (vs fresh) | 1 final.theorem (vs fresh) |
| input-rehashed | archived inputs/…/Source.lean edited, only its run_files digest rehashed | comparison reuse | – | **0 CERTIFIED** | 1 Source.lean is not the generated input |
| shape-rehashed | archived shape.json gas halved, run_files rehashed | comparison reuse | – | **0 CERTIFIED** | 1 shape.json is not the generated input |
| caveats-forged-consistent | caveats = [] in both records, rehashed | comparison reuse | – | **0 CERTIFIED** | 1 caveats (vs fresh) |
| sibling-swap-pin | swap lower()'s and raise(uint256)'s selectors in both records | comparison reuse | – | 1 functions | 1 functions |
| sibling-swap-input | shape.json points raise(uint256) at lower()'s lowered function (fn0), rehashed | comparison reuse | – | **0 CERTIFIED** | 1 shape.json is not the generated input |
| control, control2 | unedited | comparison reuse | 0 | 0 | 0 |

The bold rows were accepted by 1844041e and are rejected by 800d78a9.

## Unsupported contracts (driver 800d78a9)

Each contract in `tests/heldout/blocked/` exits 3 with `BLOCKED` before any proof work: `blocked/exits.txt`, `blocked/log/`.

| contract | exit | reason |
|---|---|---|
| Assembly | 3 | inline assembly |
| Delegatecall | 3 | external call; ABI types (bytes) |
| ExternalCall | 3 | external call; several contracts |
| Payable | 3 | value transfer |
| Reentrancy | 3 | external call |
| Selfdestruct | 3 | environment |
| StringArg | 3 | ABI types (string) |
| TryCatch | 3 | external call |

Not yet run: the SiblingOk positive that pairs with SiblingLeak (T1's acc4-siblingok run was aborted by a Hand pause, and it reruns as acc5-siblingok on 800d78a9), and one corrupted-bytes case per heldout record, once those records are published.


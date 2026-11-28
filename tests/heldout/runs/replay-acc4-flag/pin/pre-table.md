| case | what | expected | actual | rejecting check (driver's reason) | pass |
|---|---|---|---|---|---|
| stale-bytes@pin | record.json bytecode_sha256: f689833eb749e7509b4fb038bd8a4e251e77daa1 -> 1f1579b3842e5a82551d5d1d2e27698478387650 | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |
| flipped-byte@pin | record.json bytecode_sha256: f689833eb749e7509b4fb038bd8a4e251e77daa1 -> d48df2542d5ad7efb74be825259d41664b3c3d0f | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |
| changed-solar-options@pin | record.json options: ['-Ogas', '--evm-version', 'osaka'] -> ['-Osize', '--evm-version', 'osaka'] | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |
| stale-spec-hash@pin | record.json spec.sha256: 4ce5cf9a87520dc956a1e7366d5f646a07739832 -> 4de5cf9a87520dc956a1e7366d5f646a07739832 | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |
| stale-source@pin | record.json source.sha256: 4ce5cf9a87520dc956a1e7366d5f646a07739832 -> 4de5cf9a87520dc956a1e7366d5f646a07739832 | REJECTED | REJECTED | REJECTED: replay: the record's source digest is not its source file's (exit 1) | yes |
| stale-import@pin | record.json solidity_lean.inputs_sha256: {'Certified/flag_4ce5cf9a/Lowering.lean' -> 0000000000000000000000000000000000000000 | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |
| omitted-selector@pin | record.json functions: [{'signature': 'lower()', 'selector': '0 -> [{'signature': 'raise(uint256)', 'select | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |
| false-env-pin@pin | record.json environment: one frame, caller 0x2000, contract at 0x -> one frame, caller 0x0, contract at 0x100 | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |
| oog-as-revert@pin | record.json gas_bound: 3580203 -> 1790101 | REJECTED | FRESH-RUN | the manifest passed and the fresh cold run started (stopped: --no-fresh-run) (exit -15) | not run |

driver and tree unchanged across the cases: True (6d0f2621693c2c4939eaf6241406a1674b22419c:41e14e907a6ffed1d4447b26c0050bb14fcb3e3fd4d164d600c3bae73d196e75)

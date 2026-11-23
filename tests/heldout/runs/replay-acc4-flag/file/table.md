| case | what | expected | actual | rejecting check (driver's reason) | pass |
|---|---|---|---|---|---|
| stale-bytes@file | certify-record.json bytecode: another contract's fresh compile | REJECTED | REJECTED | REJECTED: replay: certify-record.json differs from the record (stale or edited run file) (exit 1) | yes |
| flipped-byte@file | certify-record.json bytecode: middle byte XOR 1 | REJECTED | REJECTED | REJECTED: replay: certify-record.json differs from the record (stale or edited run file) (exit 1) | yes |
| changed-solar-options@file | inputs/Certified/flag_4ce5cf9a/options: -Ogas -> -Osize | REJECTED | REJECTED | REJECTED: replay: inputs/Certified/flag_4ce5cf9a/options differs from the record (stale or edited run file) (exit 1) | yes |
| stale-spec-hash@file | Flag.sol: one ensures clause edited | REJECTED | REJECTED | REJECTED: replay: Flag.sol differs from the record (stale or edited run file) (exit 1) | yes |
| stale-source@file | Flag.sol: 'value = v;' parenthesised (same behaviour, other source bytes) | REJECTED | REJECTED | REJECTED: replay: Flag.sol differs from the record (stale or edited run file) (exit 1) | yes |
| stale-import@file | inputs/Certified/flag_4ce5cf9a/Source.lean: comment appended | REJECTED | REJECTED | REJECTED: replay: inputs/Certified/flag_4ce5cf9a/Source.lean differs from the record (stale or edited run file) (exit 1) | yes |
| omitted-selector@file | inputs/Certified/flag_4ce5cf9a/shape.json: first entry dropped | REJECTED | REJECTED | REJECTED: replay: inputs/Certified/flag_4ce5cf9a/shape.json differs from the record (stale or edited run file) (exit 1) | yes |
| false-env-pin@file | inputs/Certified/flag_4ce5cf9a/shape.json: env [] -> a caller premise | REJECTED | REJECTED | REJECTED: replay: inputs/Certified/flag_4ce5cf9a/shape.json differs from the record (stale or edited run file) (exit 1) | yes |
| oog-as-revert@file | inputs/Certified/flag_4ce5cf9a/shape.json: gas bound 3580203 -> 1790101 | REJECTED | REJECTED | REJECTED: replay: inputs/Certified/flag_4ce5cf9a/shape.json differs from the record (stale or edited run file) (exit 1) | yes |

driver and tree unchanged across the cases: True (6d0f2621693c2c4939eaf6241406a1674b22419c:41e14e907a6ffed1d4447b26c0050bb14fcb3e3fd4d164d600c3bae73d196e75)

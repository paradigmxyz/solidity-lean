# target-model Log

- 2026-05-11 10:40:00 PDT - status - initial owner for `L09_Evm`; target semantics currently re-export the copied bytecode/EVM model.
- 2026-05-11 11:12:25 PDT - test - EVM parity harness restored under `tests/evm/forge-parity`; command `python3 tests/bin/evm_parity.py forge`; result 21 passed.
- 2026-05-11 12:11:55 PDT - api-change - target layer refactored to `L07_Evm`; it still re-exports the copied bytecode/EVM model pending a fuller EVM semantics design.

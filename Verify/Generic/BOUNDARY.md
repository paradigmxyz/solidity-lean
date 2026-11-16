# Supported boundary of the generic driver

What decides whether a contract can come out Certified, with the code that decides it. The pins are
solar `alpharush/t1-driver-on-2637b` at c09510a39b5c9940845d2c19928c742f676b8675 (the driver,
`tools/certify/generic.py`, and the assembly fragment, `tools/certify/asm_cert.py`) and
solidity-lean 44572c15 (the Lean side). Every gate is a code path or a kernel check. None is a
fixture name or a statement shape. The driver publishes one statement, `Generic.Expected`.

A run is **Certified** only when the kernel checks `final : Statement`. Any gate below that refuses
gives **BLOCKED** (exit 3) with the feature and reason, and nothing is claimed. The source gates
run on solc's AST before anything is proved. The proof gates are the kernel's own checks, so the
boundary is what the checks accept, not this list.

## 1. Source gates (solc AST, before any proof)

| Feature | Verdict | Where |
|---|---|---|
| Imports | BLOCKED | `generic.py:114`, `:165` |
| Several concrete contracts, interfaces, abstract contracts | BLOCKED | `generic.py:169`, `:175` |
| Inheritance (any base) | BLOCKED | `generic.py:171` |
| Inline assembly | BLOCKED | `generic.py:191` |
| try/catch | BLOCKED (external call) | `generic.py:193` |
| `new` (CREATE) | BLOCKED | `generic.py:195` |
| for/while/do-while | BLOCKED: the generic source stage is loop-free and supplied invariants are not consumed | `generic.py:197` |
| payable function, constructor or fallback | BLOCKED (value transfer) | `generic.py:201` |
| Constructor with parameters | BLOCKED: `Wide.DeployedAt` runs the constructor without arguments | `generic.py:203`; `SolidCore/Refinement/Wide/Refines.lean:113` |
| receive / fallback | BLOCKED | `generic.py:205` |
| `.call`, `.delegatecall`, `.staticcall`, `.transfer`, `.send`; `.code`, `.codehash`, `.balance` | BLOCKED (external call / account read) | `generic.py:207` |
| Calls of external functions (including `this.f()`) | BLOCKED | `generic.py:213` |
| `selfdestruct`, `gasleft`, `blockhash` | BLOCKED (environment) | `generic.py:215` |
| A NatSpec clause reading `block.*`, `tx.*`, `gasleft`, `blockhash`, `chainid`, `basefee`, `coinbase` or `prevrandao` | BLOCKED: the statement fixes the environment | `generic.py:227` |
| ABI parameters and results other than `uintN`, `intN`, `bool`, `address`, `enum` (string, bytes, arrays, structs, `bytesN`) | BLOCKED | `generic.py:237`, `param_of` `:140-154` |
| No external functions | BLOCKED | `generic.py:252` |

## 2. Bytecode and fragment gates (this run's compile)

| Feature | Verdict | Where |
|---|---|---|
| CREATE, CALL, CALLCODE, DELEGATECALL, CREATE2, STATICCALL, SELFDESTRUCT, GAS, RETURNDATASIZE, RETURNDATACOPY, BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH in the runtime bytecode | BLOCKED | `generic.py:51` (`BAD_OPS`), `:258-268`, `:847` |
| The stage exporter (`-Zemit-lean-stages`) rejects the contract | BLOCKED (exporter) | `generic.py:622` |
| Final EVM IR outside the loop checker's fragment | BLOCKED (assembly fragment) | `generic.py:633`; the fragment is `asm_cert.py:488-515`: push, dup/swap below 16, stack ops of `STACK2` (`asm_cert.py:17`), iszero, not, calldatasize, jumps, labels, stop, return, revert, and the effects `FRAGMENT_EFFECTS` (`asm_cert.py:464`: callvalue, calldatasize, caller, address, calldataload, sload, sstore, keccak256) and the environment reads `ENV_READS` (`asm_cert.py:452`) |
| Memory at offsets the checker cannot bound | not supported (no certificate) | `asm_cert.static_ok`, `asm_cert.py:481`; `AssembleLoop.checkL` (`SolidCore/Refinement/Solar/AssembleLoop.lean:218`) |

## 3. Proof gates (SolidCore, solc-AST source of truth)

| Feature | Verdict | Where |
|---|---|---|
| SolidCore's type checker rejects the source | BLOCKED (source type check) | `generic.py:498` |
| The solc-AST front end refuses the source | BLOCKED (source frontend) | `generic.py:868` |
| A function's erased source tree and its MIR tree differ, or either is undefined (e.g. internal constants, `mapping(address => bool)`, a public function called internally, `>` against storage: `Tree.canon` does not orient `gt a b` as `lt b a`, early returns in pure functions) | BLOCKED (generic source check), per function | `generic.py:501`; `Generic.check` (`SolidCore/Refinement/Generic/Stage.lean:191`), `Generic.checkValue` (`SolidCore/Refinement/Generic/Value.lean:144`) |
| Constructor does not return, or emits logs | BLOCKED (constructor) | `generic.py:504`, `:506` |
| The kernel refutes or cannot finish a proof | not Certified (FAILED; resource exhaustion is reported apart) | `generic.py:47` (`RESOURCE_MARKS`) |

## 4. What a Certified statement covers

* **Calls**: every external function, any argument words below `2^256`, any value below `2^256`
  (`genericValid`, `Verify/ShapeGeneric.lean:168`), from any storage that writes the constructor's
  slots, in the **default context** (caller 0x2000; `generic.py:40` `ENVIRONMENT`). The **any-caller
  form** (Verify/Generic/AnyCaller.lean) covers **every caller** below `2^160` other than the
  contract, on the calls **without value** (`genericValid0`, `Verify/ShapeGeneric.lean:212`), for a
  contract that passes `callerFree` (no function's erased tree reads `msg.sender`) and whose
  bytecode reads neither CALLER nor KECCAK256 (`cert.env = false`, `cert.reads = false`).
* **Fixed, recorded, not quantified**: the contract's address 0x1000, the block and the transaction
  of `Target.message`.
* **Gas**: observable equality from the loop checker's bound on. This does not separate
  out-of-gas from an empty revert.
* **Out of scope (never Certified)**: the constructor and init code, the lifecycle (constructor
  establishment of an invariant, preservation by every entrypoint), reentrancy, calls to other
  accounts.

## 5. Any caller: what is proved and what is missing

Proved (kernel, standard axioms):

* `AssembleLoop.within_of_checkLFrom` and `forward_of_checkLFrom` (Verify/Generic/CheckLFrom.lean):
  the loop checker's two bytecode edges for a message from any account `a` other than the contract.
  The proofs are `run_simL`, `within_of_checkL` and `forward_of_checkL` with the caller generalised.
  No premise is added.
* `translationAt_ofL`: the translation in any context, from a stage of `solidCoreFrom a` to the final
  EVM IR.
* `callerFree`, `runFrom_eq_of_callerFree`, `translationAt_callerFree`, `specProof_callerFree`.
* `Instances.FlagAnyCaller.expected`: the accepted held-out Flag, `Expected` with
  `Contexts := Context.Ok` over the driver's exact bytes.

Missing, with the interface each needs:

* **Value from other callers.** `Generic.stageAtValueWith`
  (`SolidCore/Refinement/Generic/Value.lean:153`) is stated for `solidCore fuel`, which is
  `Source.run` from `callerAddress`. Needed: the same theorem for `solidCoreFrom a fuel`, i.e.
  `source_run_value` with `Source.runFrom a`, the counterpart of `source_run_from`
  (`SolidCore/Refinement/Generic/StageFrom.lean:298`).
* **Contracts that read `msg.sender`.** `Generic.stageFrom` (`StageFrom.lean:371`) gives the source
  stage for every caller under `checkSym` and an oracle with `FromOk a`. Needed: (1) the driver
  emitting `checkSym fuel mirFuel coreLit stage0 fns = true`; (2) solar-tv's backend stage
  `mirSem (O a) → evmirSem (O a)` for an oracle family (the generated `*_mir_to_evmir` is stated at
  `Shapes.oracle`); (3) `cert.env = true` with `OracleOkAt a (O a)`. `translationAt_ofL` already
  takes all three.
* **The specification's context.** The exported spec evaluates `msg.sender` through `ctxOfCall`,
  the default sender. Any-caller specs that mention the sender need `ctxOfCall` to take the context.

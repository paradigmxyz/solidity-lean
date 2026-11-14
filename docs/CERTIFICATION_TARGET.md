# Certification target: final theorem and interfaces (v1, 2026-11-14)

## The one statement we publish per contract slice
For a pinned input triple (source file + sha256, solar-verify spec annotations, compile options `-Ogas --evm-version osaka`)
and the runtime bytes `code` that the solar binary built in the same run emits (byte-equal, fresh, never a reference artifact):

    Certified EthLib code Valid Allowed Post G   -- Verify/Shapes.lean
      inhabited : ∃ call, Valid call
      equiv     : Equiv      -- every Valid call: EVM run of code ≈ SolidCore run of src (storage, return data, revert data, logs)
      terminates: Terminates -- every Valid call: the source run terminates (ranking certificates, no fuel-as-proof)
      meets     : Meets      -- every Valid call: Post holds of the source result (success or an Allowed revert)
      resources : Resources  -- every Valid call with gas ≥ G runs out of gas never; G is a proved bound

with every premise printed in the statement and the transitive axioms only propext, Classical.choice, Quot.sound.
The driver states this type, checks the proof term against it, replays the closure in the kernel and binds `code`.

## The chain, edge by edge (what is proved vs trusted)
| Edge | From -> To | Status rule |
|---|---|---|
| E0 port | upstream v2-core (0.5.16) -> pinned 0.8 port (port.py text edits) | TRUSTED boundary, stated. Not an equivalence proof for upstream. |
| E1 frontend | port .sol -> solc AST -> Source.lean (uniswap_v2_sources.py, solc_ast_to_lean_source.py) | TRUSTED frontend (TCB). uniswap_v2_core.py checks the AST import/typing only. Regenerating or hashing Source.lean does not prove it denotes the source. |
| E2 semantics | Source.lean -> SolidCore run | definition: the meaning of the source |
| E3 source -> MIR | SolidCore run -> MIR stage0 run | PROVED per contract by the generic source checker (contract_ok / checkC*) |
| E4 MIR -> EVM IR | stage0 -> sched -> evm1..n | PROVED per stage (stage certificates) |
| E5 EVM IR -> bytes | evm_n -> executed exact runtime bytes (Assemble.check, AssembleCallSeg) | PROVED; its runner premises (StaticRunner, CalleesRun) must be discharged, not assumed |
| E6 binding | statement's `code` = fresh solar output | driver byte equality + leanchecker replay |
| E7 spec | solar-verify spec -> VC over SolidCore runs -> discharged -> transferred to bytes via E3..E5 | PROVED; spec non-vacuous (NonVacuous), mutants refused by execution |
| E8 resources | gas bound on EthLib run of code | PROVED bound G, separate from functional equivalence |

Strongest status (CERTIFIED) requires E3..E8 proved for the named scope. Any missing edge blocks it and is reported by name.
Handwritten specs, ghost state, abstraction functions, loop invariants and proof scripts are proof aids and are fine.
A hand-maintained functional model of the contract is NOT a substitute for E1..E5: without a checked correspondence it is a lemma.

## Hash premises
Global separation over all 160-bit keys of a nested mapping is unsatisfiable: `NestedSlotsSeparated` (Verify/Spec/TreeMapNested.lean)
makes `(a, c) ↦ keccak(a . keccak(c . n))` injective on 2^320 pairs into 2^256 words, so any theorem assuming it is vacuous for real EVM.
Replacement: separation scoped to the finite set of preimages a call touches (its keys and the slots its frame states), as hevm does
(pairwise injectivity over the hash applications that occur, not a universal axiom). Single-level maps over 160-bit keys have no such
cardinality obstruction but are still a named computational assumption, printed in the statement.

## First slice: UniswapV2ERC20.transfer (scope named; never advertised as Uniswap)
Valid: selector transfer(address,uint256), well-formed calldata, callvalue 0, ANY caller, any to and value, any storage.
Post, as sequential storage updates in source order (debit the caller, then credit the recipient reading the debited state):
- caller != to: success iff balanceOf[caller] >= value and balanceOf[to] + value < 2^256; then balanceOf[caller] -= value,
  balanceOf[to] += value.
- caller == to: success iff balanceOf[caller] >= value (the credit reads the debited slot, so it cannot overflow);
  balanceOf is unchanged. No recipient-overflow condition applies.
- on success: Transfer(caller, to, value) logged, returns true, every slot outside the call's footprint unchanged;
  otherwise revert with the source's revert data and no state change.
Required concrete cases: balance = 2^256-1, value = 1, caller == to succeeds with balance unchanged and Transfer emitted;
self-transfer with balance < value reverts.
Premise: balanceOf slot separation scoped to the call's footprint {caller, to}: the exact premise is printed in the statement,
with a satisfiable instance exhibited in Lean. The frame is stated over the footprint and the slots the source writes; it must
not quantify over "all other slots" in a way that reintroduces collision-freedom for every key. No external calls:
StaticRunner/CalleesRun discharged.
Negative controls by execution: altered bytecode/jump, missing debit, wrong post, mismatched environment.

## Reclassified (kept as lemmas until connected)
- Contracts/UniswapV2/PairSpec/Published.lean published_of_stages: composition interface taking every stage as a hypothesis. Not a Pair proof.
- PairSpec Negative.lean: formula checks on example states, not mutated program executions.
- Factory/Create2 lemmas: createPair is OMITTED from the Factory source (create2 of creationCode is outside the frontend fragment). Blocked on E1.
- ERC20 EndToEndAll.published: vacuous (NestedSlotsSeparated), StaticRunner/CalleesRun assumed, its generated stage modules are not in the CI build.

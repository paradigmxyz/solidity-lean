# Frontend boundary (E1): why the importer reads solc's AST, and a checked HIR shadow

Design note. Base: this repository at `49ef3c4b`, solar at `902cccc2`. It changes nothing: the
solc-AST importer, E1's TRUSTED status (`docs/CERTIFICATION_TARGET.md`) and every proof stay as they are.

## Why the importer reads solc's AST

No recorded decision rejects solar's HIR: `git grep -i hir` and `git log -S HIR` find nothing here. The
choice is historical, and it follows the project's design:

- **Start (`a55a0e1c`, 2026-05-11).** The project began as an executable semantics of Solidity checked
  against pinned solc and Forge. The first ROADMAP says "Solar output, solc JSON, and Forge fixtures are
  ingestion or test evidence until Lean rechecks them", and "Solar, solc JSON, or another parser may build
  candidate syntax, but Lean must recheck names, types, scopes, storage locations". The progress log notes
  that no local solar binary was installed.
- **Importer (`e53af675`, 2026-07-06).** `scripts/solc_ast_to_lean_source.py` arrived as a "harness
  frontend, not trusted semantics" of the differential corpus, whose oracle is pinned solc (99 paired
  cases, ~311 rejection lanes). Reading the oracle's own analyzed AST makes acceptance agree by
  construction; many entries in `docs/DECISIONS.md` rely on "solidity-lean only ever receives programs
  solc already accepted". The importer is mostly syntactic; the Lean type checker re-derives names, types,
  selectors (kernel-checked Keccak) and storage fields.
- **Certification (`7cdf5548`, 2026-11-12; `d5daff52`, 2026-11-13).** solar became the backend being
  certified months after the frontend existed, and the edge table recorded the existing frontend as E1.
- **solar side.** solar has no serialized HIR. `crates/codegen/src/lean_stages.rs` exports from the first
  lowered MIR (`Stage0`) on; solar-verify reads the parsed AST, not the HIR. solar's solc-compatible AST
  JSON, with IDs, types and resolutions read from the HIR (solar `e361755ea`, #2344), landed on
  2026-11-13 and is unused here.

## Why HIR must not become the source of truth

E3 is valuable because `Source.lean` and solar's MIR come from frontends with separate lineage: solc
plus this repository's importer and type checker on one side, solar's parser, `ast_lowering` and sema on
the other. A solar frontend bug (wrong overload, C3 order, slot packing, getter or selector) today shows up
as an E3 failure. If the source model were built from solar's resolution, the same code would decide what
the source means and what is compiled; such a bug would appear on both sides of E3 and pass. Adopting
HIR as source truth therefore narrows bug-catching. So: keep the importer and the independent
source -> MIR checker, keep E1 an explicit trusted boundary, and use HIR only as a **shadow** that is
compared, never imported.

Note what E1 means today: E3..E5 relate `Source.lean` to the exact bytes, so an E1 error does not make
the bytes theorem false. It makes it a theorem about a program other than the one a reader reads in the
`.sol`, with the spec's names, selectors and slots possibly bound to the wrong things.

## Design: versioned HIR shadow export and checked correspondence

**Export (solar).** A new opt-in output, `hir_facts.json`, written in the same run that emits the stages,
listed in the stage `manifest.json`, with `"version": 1` (a change of field or meaning is a new version,
as in `crates/verify/LEAN.md`). It fails closed: a fact it cannot state is an error, never dropped.

- binding: source path and sha256, solar commit, options, contract name;
- contract: kind, linearized bases;
- state variables in declaration order: name, canonical type, slot, offset, bytes, constant or immutable
  (from the existing storage-layout query, which matches solc's);
- functions and getters: declaration path, canonical signature, selector, visibility, mutability,
  parameter and return types with locations, applied modifiers, the declaration each override resolves to;
- events and errors: signature, topic 0 or selector, indexed flags;
- internal call graph: for each function, the callees by declaration path;
- spec vocabulary: each identifier the spec annotations use, resolved to its declaration.

It leaves out bodies and expression types: it states interface and binding facts, not semantics.

**Checker (Lean).** The facts become a generated Lean term (as the stages are), and one kernel check per
contract compares them with the `CheckedContract` of `Source.lean`:

| Check | Agreement required |
|---|---|
| A1 dispatch | same external functions; equal signatures; both selectors equal Keccak of the signature |
| A2 storage | for every field, SolidCore's (slot, offset, type) equals the export's |
| A3 events, errors | equal signatures, topics and indexed flags |
| A4 inheritance | equal linearization; each selector dispatches to the same declaration |
| A5 call graph | equal internal callees per function |
| A6 spec names | each spec identifier denotes the same declaration on both sides |

A mismatch fails with the named fact. The claim is agreement of two independent frontends on these facts,
not frontend correctness. E1 stays TRUSTED; `record.json` gains `frontend_agreement: checked (A1..A6)`
or the failing check.

## What it shrinks, and what it does not

It shrinks: for selectors, ABI types, storage layout, inheritance, dispatch and call targets, and the spec's
vocabulary, the trusted claim goes from "solc's AST and the importer are right" to "they are right, or wrong
in the same way as solar's independently written sema". These are the facts a reader uses to map the
theorem's `Valid` calldata and `Post` slots back to the `.sol`.

It does not shrink: expression meaning (evaluation order, checked arithmetic, conversions, constant folding)
or the parse of the text itself; a misreading of the language that both frontends share; E0.

A cheaper partial step: render `Source.lean` a second time from solar's solc-compatible AST JSON through
the same importer and require the same output up to node IDs. It compares the two ASTs, not the importer.

## Cost (est.)

- solar: 300-500 lines in `crates/sema/src/output` over queries that exist (storage layout, ABI and
  selectors, resolutions), plus one UI test per example.
- Lean: the facts embedding and checker, 400-600 lines; per contract one generated facts file and one
  decidable check over short lists (seconds).
- Driver: one more output in the same solar invocation and one manifest binding; no extra build.
- Upkeep: canonical type strings must stay aligned with SolidCore's `Ty`; this is the main recurring cost.

Sequencing: no prototype and no builds until the transfer acceptance is unblocked.

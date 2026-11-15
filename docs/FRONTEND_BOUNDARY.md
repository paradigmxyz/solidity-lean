# Frontend boundary (E1): why the importer reads solc's AST, and a checked HIR shadow

Design note and Counter prototype. Bases: this repository at `bc6da61b`, solar at `902cccc2`. The
solc-AST importer, E1's TRUSTED status (`docs/CERTIFICATION_TARGET.md`) and every proof stay as they are.
The prototype's code (`Verify/HirShadow`, solar's `tools/hir-shadow`) lives only on the branches
`alpharush/hir-shadow` of both repositories (solidity-lean `29eb2ad3`, solar `796368ac`), not in this tree.

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

## Design: HIR shadow facts as checked hints

The source -> MIR foundation stays `SolidCore/Refinement/Generic/Stage.lean` (source model against
solar's first lowered MIR). The HIR shadow adds no frontend and no interpreter: it is an optional,
versioned list of interface facts that solar states and Lean either matches against the independent
source model or refuses. Nothing downstream reads a fact that was not matched.

**Export (solar, `tools/hir-shadow/hir_shadow.py`).** One Standard JSON compilation that stops after
analysis gives the AST JSON (IDs, types, selectors and resolutions read from the HIR), the storage
layout, the method identifiers and the ABI. The script writes `hir_shadow.json` (`format:
solar-hir-shadow`, `version: 1`) and its Lean term, bound to the solar commit, the binary's sha256
and the source's sha256:

- state variables that take storage: name, canonical type, slot, offset, bytes;
- functions, public getters and the constructor, in declaration order: kind, canonical signature,
  selector (external and public only), visibility, mutability, ABI input and output types.

Facts two outputs both state must agree (an AST `functionSelector` and its method identifier), or
nothing is written. A contract outside the envelope (inheritance, non-value state, modifiers,
events, errors, user types, receive or fallback) exits 2 with `BLOCKED` and the reason.

**Check (Lean, `Verify/HirShadow`).** `check sel c f` derives the same list from the solc-AST
`ContractDecl` alone: solc's packing rule for value-typed storage, canonical types and signatures,
and `sel signature` for selectors. The verdict is `agree` only on exact equality; any difference is
`rejected` with the first differing entry; a contract outside the envelope is `blocked`, never
agreed. Each selector solar states is proved Keccak-256 of its signature by one kernel evaluation
before the check runs (`selector_eq`), so a wrong selector already fails there.

**Counter prototype.** `Verify/HirShadow/Counter.lean` proves `check keccak decl facts = .agree`
for solar-verify's Counter (`Certified/verify_counter/verify_counter.sol`, whose source model is
`Contracts/VerifyCounter/SourceAst.lean`), and rejects six one-fact mutations (a slot, a selector, a
type, the order, the contract, the version); adding a mapping to the source model is `blocked`.

## What it shrinks, and what it does not

E1 stays TRUSTED: agreement is evidence, not a premise removed. For the facts it covers (selectors,
ABI types, storage layout), a frontend error must now be shared by solc's AST, the importer and
solar's independently written sema to go unnoticed. It does not touch expression meaning, the parse
of the text, a misreading both frontends share, or E0.

solar's own solc-compatible AST JSON is never used as the independent source: it is solar's reading,
and the shadow uses it only on the hint side.

## Measurement: does the shadow reduce matching? NO-GO for expansion

`Generic.Stage` (`check`) matches nothing by name. Per selector it compares the erased SolidCore tree
with the symbolic run of solar's first lowered MIR, and that run enters internal callees by function
index (`symCallee`). Dispatch, storage slots and callees are already checked by tree equality. To
see what hints could add on a real bridge case, the lowered MIR (`-Ogas --evm-version osaka`,
solar `902cccc2`, `-Zdump=mir-final`) of the Uniswap V2 port (`solar-tv/uniswap-v2/port.py`) was
counted:

| Contract | MIR functions | internal calls left (`icall`) | callees needing a name match | overloaded source names |
|---|---|---|---|---|
| UniswapV2ERC20 (transfer regression) | 20 | 6 (`_transfer`, `_approve`, `sub`, 2 each) | 0 | 0 |
| UniswapV2Pair | 64 | 67 (`mul` 17, `sub` 14, `_safeTransfer` 6, ...) | 0 | 0 |
| solar-verify examples (ArrayMax, Bugs, Counter, Token, Vault, struct_slot) | 3 to 10 | 0 | 0 | 0 |

Every callee is reached by index, so callee and dispatch hints would remove no matching step. The
remaining gaps are semantic, not matching: loops (`ArrayMax`, `Counter.bump`) need invariants and a
bridge between source and MIR loops. The HIR's desugaring does not rule out loop, cutpoint or
source-location hints; the measured limit is that this prototype supplies no invariant or bridge
evidence, so it does not close that gap. Hints of that kind would stay untrusted and be checked
against the independent source semantics, which remains the source of truth. The interface
facts give one real benefit: diagnostics. A wrong slot or selector fails `Generic.Stage` as an
unequal tree, while `Verify.HirShadow.check` names the fact (`storage differs at 1 (limit)`).

Decision: NO-GO on expanding the architecture around HIR for the current direct checker
(`Generic.Stage`). Keep the Counter prototype as an optional agreement check on its branch, outside
CI and the trusted base. Revisit if a contract fails `Generic.Stage` for a reason that a matched fact
would resolve, or if loop or cutpoint hints come with invariant or bridge evidence the kernel checks.

## Cost (measured on the hosted Hand, 5 CPUs)

- Code: `tools/hir-shadow/hir_shadow.py` in solar (245 lines, no Rust change; one `exclude` entry in
  the workspace `Cargo.toml`), `Verify/HirShadow` on the branch (275 lines, plus 70 generated per contract).
- Run: the export is one Standard JSON compilation (under a second for Counter). The Lean check
  needs `Contracts.VerifyCounter.SourceAst`'s closure (336 s cold, Mathlib from cache); the three
  HirShadow modules then build in 5 s, one kernel Keccak evaluation per selector.
- Upkeep: canonical type strings must match between the script and `Verify.HirShadow.canon`.

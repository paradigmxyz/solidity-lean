# G0: the source-text bridge

G0 states a contract's certified theorem about the **bytes of its source file**. It is a
candidate bridge experiment over a small, declared grammar. It does not complete source to
bytecode.

    bytes ──read (G0, Grammar.lean)──▶ Reading ──Reading.source / Reading.spec──▶ Expected src spec rt
       │                                  ▲
       └── digest (sha256, kernel)        └── equal, by the kernel, to the importer's AST and the
                                              spec exporter's bundle of the same bytes (agreement)

* `Grammar.lean`: `read : List Nat → Option Reading`, the reference reader. It lexes, parses one
  contract, and returns SolidCore's `SourceUnit`, the ABI with kernel-computed Keccak selectors,
  the solar-verify spec bundle of its NatSpec tags, and the constructor's storage.
* `Bridge.lean`: the generic constructors `Reading.source` and `Reading.spec`, the same for every
  contract, with no name, hash or shape dispatch; `SourceStatement`; `statement_of_agree` (the only way
  in: a generic transport conditional on `Expected`, which it takes as a premise; Flag's instance
  discharges it with the record's proved `Final.final`); `bytecode_meets` (row P on the exact
  runtime bytes).
* `Run.lean`: `runTree`, one kernel-evaluable computation of a reading's call for every contract, and
  `run_eq_runTree`: its result is SolidCore's `Source.run`, by the generic `Generic.source_run`.
* `Instances/Flag.lean`: Flag (rc2-acc5-flag), with its certificate proved by the record's
  modules. Those come from the immutable record (DEPENDENCIES.md): `flag_record.sh` assembles them
  into `Certified/flag_4ce5cf9a` and checks all 33 files against `FLAG_RECORD.sha256`.
* `Tests.lean`, `TestRuns.lean`, `Cases/`, `gen_cases.py`, `check.sh`: the tests. `Audit.lean`
  and `AuditFlag.lean`: the production closure's axioms.

## Supported grammar (G0 v0)

These constructs, and nothing else. Any other input reads as `none` (fail closed):

* `//` comments, and `///` lines, whose text is NatSpec;
* `pragma <name> <value>;` at file level;
* one `contract <Name> { ... }` with no bases;
* state variables `uint256 public <name>;` with no initializer;
* functions `function <name>(uint256 <p>, ...) external { <x> = <y>; ... }`, where each `<y>` is an
  identifier or a decimal literal;
* on a function, NatSpec lines that are free text, `@custom:succeeds-if <e>` or `@custom:ensures <e>`,
  with `<e>` built from decimal literals, parameters, state variables, `msg.value`, `old(<e>)`, `==`,
  `&&` and parentheses.

Support matrix. Everything below reads as `none`:

| construct | G0 v0 |
|---|---|
| `uint256 public` state variables, no initializer | supported |
| external functions of `uint256` parameters, assignments of identifiers or literals | supported |
| `succeeds-if` / `ensures` with `==`, `&&`, `old`, `msg.value` | supported |
| mappings | unsupported |
| `require`, `revert`, `assert` | unsupported |
| arithmetic, comparisons other than `==` in specs, any operator in bodies | unsupported |
| `if`, loops | unsupported |
| `msg.sender` and every other environment read | unsupported |
| initializers, constructors | unsupported |
| returns, view functions, other types and visibilities | unsupported |
| events, modifiers, inheritance, imports, several contracts | unsupported |

The tests cover two sources and their mutations. They are not coverage of arbitrary contracts,
even within v0.

## What each check shows, separately

| row | what it shows | how | trusted beyond Lean's kernel |
|---|---|---|---|
| parsed | G0 reads the bytes to some reading, or to `none` | kernel (`kernel_rfl`) | nothing |
| digest binding | the bytes' sha256 is the recorded digest | kernel (`decide +kernel`) | nothing |
| reading agreement | G0's reading equals the importer's AST, the spec exporter's bundle and solc's ABI of the same bytes | kernel | nothing (the upstream outputs are frozen data, not trusted) |
| denotation (run) | a mutation's run, SolidCore's `Source.run`, differs from the original's | kernel (`runTree`, `run_eq_runTree`) | nothing |
| property (row P) | the exact runtime bytes meet the spec for every valid call | `Expected`, proved | the record's certificate (proved, not assumed) |

Binding to the original bytes is not correctness of parsing: a matching digest or a reading that
agrees with upstream does not show that G0's parse and desugaring are Solidity's meaning. **G0 is
the trusted reference frontend** for statements made through it.

Each run is checked by two kernel routes. `runTree` evaluates the call's erased branch tree, and
the existing `Generic.source_run` proves that this is `Source.run`'s result. `Direct` evaluates
`Source.run` itself, rewriting the hash map's `USize` index with the existing `Verify.VC.mkIdx_eq`.
Without that rewrite the index does not reduce well, an implementation limit rather than a
limit of the kernel. Neither route adds an interpreter, a storage model of its own or an axiom. It covers contracts
whose constructor leaves empty storage, and functions `eraseFn` erases.

**Axiom policy.** `Audit.lean` walks every constant of every `Verify.SourceText` module it imports
(and `AuditFlag.lean` with Flag's instance) through `Lean.collectAxioms` and fails on anything
outside propext, Classical.choice and Quot.sound, including native_decide's axioms and sorry.
No module of the branch uses native evaluation.

## Cases

Two independent sources. Flag is the record's source. LedgerRelay was chosen by independent
acceptance before any test ran, and its bytes were frozen (sha256 8c89354e…2f6d). The mutations
are fixed text edits in `gen_cases.py`. The pinned upstream frontend (solc 0.8.35 AST through
`scripts/solc_ast_to_lean_source.py`, solar-verify `--emit-lean-spec`, solc `--hashes`) accepts all 17.

| case | edit | expected | theorem | check |
|---|---|---|---|---|
| LedgerRelay | none | parses, agrees, digest | `original_agrees`, `digest_eq` | kernel |
| LedgerRelayAlpha | consistent renaming of contract, variables, parameters | parses, agrees with its own upstream | `alpha_agrees` | kernel |
| LedgerRelayLayout | comments and whitespace | parses, agrees with its own upstream | `layout_agrees` | kernel |
| LedgerRelayBody | `stamp = 17` → `18` | parses; rejected against the original | `body_agrees`, `body_rejects` | kernel |
| LedgerRelaySpec | ensures `stamp == 17` → `18` | parses; rejected | `spec_agrees`, `spec_rejects` | kernel |
| LedgerRelayName | `setPair` → `setPairs` | parses; rejected (ABI) | `name_agrees`, `name_rejects` | kernel |
| LedgerRelaySwap | relay's first two statements reversed | parses; rejected: `relay(9)` from `right = 7` gives `left = 9`, the original `left = 7` | `swap_agrees`, `swap_rejects` | kernel |
| LedgerRelayCaller | a succeeds-if → `msg.sender == 0` | `none` | `caller_closed` | kernel |
| LedgerRelayStorage | `left` initializer `= 1` | `none` | `storage_closed` | kernel |
| LedgerRelayRequire | `require(a == a);` in setPair | `none` | `require_closed` | kernel |
| Flag | none | parses, agrees, digest = record's, certificate transported | `original_agrees`; `Flag.digest_eq`, `flag_source_text` | kernel |
| FlagBody | `raised = 1` → `2` | parses; rejected | `body_agrees`, `body_rejects` | kernel |
| FlagSpec | an ensures literal changed | parses; rejected | `spec_agrees`, `spec_rejects` | kernel |
| FlagName | `raise` → `raises` | parses; rejected (ABI) | `name_agrees`, `name_rejects` | kernel |
| FlagCaller, FlagStorage, FlagRequire | as for LedgerRelay | `none` | `*_closed` | kernel |

A rejection means the mutation's reading is not the frozen original's, so `statement_of_agree`
cannot carry the original's certificate to it. Each rejection shows what differs (a run, the
ensures' literals, the ABI), never the hash. A parser refusal is never counted as a rejection.
A regenerated, internally consistent certificate for a renamed valid program would be valid;
these tests do not claim otherwise.

**Property row for LedgerRelay: NOT RUN.** No `Expected` of LedgerRelay is proved, so no LedgerRelay
instance of `statement_of_agree` exists. The swap mutant reaches the denotation check (the runs
above), not a property check. Row P exists only for Flag, through its proved certificate. What a
LedgerRelay certificate still needs is in DEPENDENCIES.md.

## Trusted computing base, for Flag's statement

Before (the record's own statement): solc's AST, the importer
(`scripts/solc_ast_to_lean_source.py`), the port and flattener, and the spec export
(`solar-verify --emit-lean-spec`); the statement was about the importer's output, and the
source text's link to it was the digest of what certify read.

After, for `flag_source_text : SourceStatement bytes …` (a statement of the bytes):

* trusted: **G0** (`Grammar.lean`) as the meaning of the text in its grammar; SolidCore's semantics
  and the spec semantics, as before; Lean's kernel;
* no longer trusted for this statement: the importer and the spec export, whose outputs the
  kernel checks equal to G0's reading; the port and flattener (Flag is one file, read directly);
* not used by the statement: `importedSourceName`. It is a label outside `importedSourceUnit`,
  and no other module of the record refers to it;
* solc: only as the compiler whose AST the importer reads, now checked rather than trusted. G0
  computes selectors itself (`Cases/Selectors.lean`, Keccak by the kernel).

This replaces trust in the importer and the spec export with trust in G0. It does not remove
frontend trust: G0's correctness against Solidity is OPEN. The frontend-correspondence item is
closed only in the form "the importer and the spec export agree with G0 on Flag's exact bytes".

## Running

    Verify/SourceText/check.sh SOLC SOLAR_VERIFY [--flag]

It checks the pinned upstream tools, regenerates the cases and compares them with `CASES.sha256`,
builds `VerifySourceText`, audits the production closure's axioms, checks unaltered copies (must
pass), tampered expectations and tampered audits (must fail). With `--flag` it also assembles the
Flag record (`flag_record.sh`), builds `VerifySourceTextFlag` and audits it. It exits 0 when every row
matches. A clean checkout needs nothing else; DEPENDENCIES.md lists every input.

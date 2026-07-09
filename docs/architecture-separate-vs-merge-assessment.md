# Architecture assessment: separate Solidity-semantics repo vs. merge into evm-compiler

**Date:** 2026-07-08
**Author:** Fable software-architecture assessor (read-only investigation of both repos)
**Question:** Should the Solidity source semantics (`solid-core-spine` / "Solidus") be merged
into `evm-compiler` as a `solidity-semantics/` subfolder (renaming the combined repo
`solidus`), or kept structurally separate?

---

## (a) Recommendation

**Keep them SEPARATE, and formalize the edge as a Lake git dependency — the "separate-repo-dependency" option.**
Structure the source semantics exactly the way the *target* semantics is already structured:
a standalone, versioned, citable Lean library that the compiler `require`s from git, precisely
as `evm-compiler` already does `require evmyul from git "…/EVMYulLean.git" @ "3c5c44a…"`. Do
**not** inline it as a subfolder, and do **not** (yet) fold everything into a single monorepo.
The decisive facts are that (1) the target spec (EVMYulLean) is already an external dependency,
so symmetry wants the source spec to be one too; (2) the two artifacts are **definitionally
decoupled today** — the compiler's public correctness theorem does not reference `SolidCore`
at all, and `SolidCore` does not reference the compiler; and (3) the source semantics evolves
on a **solc/Forge differential clock**, not a compiler clock, so atomic cross-cutting commits
are rarely needed. Monorepo-multi-package is the correct *fallback* and becomes the right answer
only if and when a genuine end-to-end Solidity→EVM theorem enters sustained co-development
(see §(d)). The subfolder-merge he prototyped is the weakest of the three and should be dropped.

---

## (b) Evidence gathered (both repos, concrete findings)

### The target spec is already an external Lake dependency (the precedent)
`/Users/dan/Projects/evm-compiler/lakefile.lean`:
```
require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "3c5c44a62f4e7964bd1bc648caa708a111664c84"
```
Confirmed pinned in `evm-compiler/lake-manifest.json` (`"name": "evmyul"`, `"inherited": false`).
The EVM + Yul *target* semantics is a standalone library the compiler **depends on**, not code
that lives inside the compiler. `solid-core-spine/lakefile.lean` *also* already requires `evmyul`
from the same pinned git rev, plus a path dep `require «evm-interaction» from ".." / "evm-interaction"`.
So multi-package Lake composition (git deps + path deps + a hash-parity guard) is already the
established idiom in this project.

### The compiler does NOT depend on the Solidity source semantics today — the edge does not yet exist
- No `require` of solid-core / SolidCore in `evm-compiler/lakefile.lean` or `lake-manifest.json`.
- `grep -rn "import SolidCore" evm-compiler` → **zero hits.**
- `evm-compiler` *does* have an `EvmCompiler/Solidus/` directory and many `Solidus*` files, but
  this is a **name collision, not a shared artifact.** `EvmCompiler/Solidus/Defs.lean`,
  `SourceRun.lean`, `Bridge.lean` build entirely from `EvmCompiler.Solidity.RawAst…`,
  `EvmCompiler.Yul…`, `EvmCompiler.Assembly…`, and the pinned `EvmYul` — never from `SolidCore`.
  It is the *frozen public-spec vocabulary for the compiler's own "Solidus Arena" optimization
  challenge*, unrelated to `solid-core-spine`'s `SolidCore`.

### What the compiler's correctness theorem actually refines against (the crux)
`EvmCompiler/Correctness.lean` — `Solidus.compile_correct` — states its source side as
`Solidity.RawAst.Raw.SourcePreservation.rawObjectRun`, i.e. **the independent Yul semantics of
the object decoded from solc Standard-JSON** (`execObjectCode … contextForObject`). The module
header lists what a reader must trust: the pinned `EvmYul` interpreter, "the Yul source semantics
(`…rawObjectRun`)", the `Simulation` framework, and `EvmCompiler/Solidus/Defs.lean`. **`SolidCore`
appears nowhere.** The compiler today proves **Yul(solc-output) → EVM**, not **Solidity-source → EVM**.
This means the Solidity-language semantics in `solid-core-spine` is *not currently on the compiler's
proof path at all* — the coupling the merge would "consolidate" does not exist yet.

### Dependency direction from the source side is clean and one-way
`grep` for `evm-compiler|EvmCompiler|compiler` under `solid-core-spine/SolidCore` returns only
precompile-address references (`SolidCore.Solidity.Shared.Precompile.*`), never the compiler.
`SolidCore/README.md`: "The former compiler pipeline layers have been removed from this branch."
`solid-core-spine` deliberately shed compiler concerns; it is a pure source-language spec plus
its validation corpus.

### What drives changes in `solid-core-spine` (co-evolution clock)
Recent history is uniformly **solc-differential-driven**, not compiler-driven:
`gap/ec1: abi.encodeCall selector+encoding`, `CE-family constant folder matches solc
ConstantEvaluator`, `CB1+A2 try/catch dispatch by revert kind`, `AGG1/2/3 storage-aggregate
layout`, `FB1 bytesN shift/bitwise-not lane cleanup`, `contest: validate events+storage parity`.
The corpus is large and self-standing: **732 `.sol` cases** under `tests/`, plus a
`forge-harness/`, `solidity-interpreter/`, `e2e-proofs/`, and `contest/`. The thing this repo is
validated against is **pinned solc 0.8.35 + Forge**, never the compiler.

### The prototyped merge is cosmetic, not a real composition
`/Users/dan/Projects/solidus` (the POC) is a two-root history/file join: `solidity-semantics/SolidCore`
exists, but the top-level `solidus/lakefile.lean` still only `require`s `evmyul` and declares
`lean_lib «EvmCompiler»` — **the `solidity-semantics/` subfolder is not wired as a Lake package
and is not built.** So the POC proves *file colocation* is feasible; it does **not** demonstrate the
two semantics actually composing in a build. Whatever integration value a merge promises is still
unbuilt even in the prototype.

### Feasibility of the dependency edge
All three packages are on the **same toolchain, `leanprover/lean4:v4.28.0`** (`solid-core-spine`,
`evm-compiler`, `evm-interaction`), and all pin the **same `evmyul` git rev**. A
`require solidus from git … @ <rev>` edge is mechanically trivial and matches infrastructure
already in place.

---

## (c) Tradeoff analysis across the six axes

**1. Dependency direction & coupling.** Zero definitional coupling exists today (no import either
direction). The only realistic future edge is *compiler → source-spec*, i.e. the compiler
consuming `SolidCore` to state a full Solidity→EVM theorem. That is exactly the shape of the
existing *compiler → evmyul* edge. Coupling is therefore naturally expressed as a **dependency**,
not a co-location. **→ favors separate-repo-dependency.**

**2. Refinement structure.** A full compiler-correctness statement ("compiled EVM refines the
Solidity source semantics") references BOTH specs. In the existing theorem the target spec is
imported as the external `evmyul` dependency while the compiler's own vocabulary is local. By
symmetry, the source spec `SolidCore` should be imported the same way — an external dependency —
with the end-to-end theorem living in the **compiler** (the artifact being verified), importing
both specs. Nothing about the theorem wants the source spec's 500+ commits, 732-case corpus, and
Foundry harness compiled into the compiler. **→ favors separate-repo-dependency.**

**3. Co-evolution frequency.** Source-semantics changes are solc-differential-driven and today
touch the compiler **never** (no edge exists). Even once an end-to-end theorem exists, a
spec change would bump a pinned rev and possibly break a downstream proof — the normal, healthy
signal of a spec/implementation boundary, not a reason to fuse them. Atomic cross-cutting commits
would be valuable only during intense simultaneous development of the bridge proof itself.
**→ favors separate today; mild pull toward monorepo only during active bridge work.**

**4. Standalone-artifact value.** `SolidCore` + its pinned-solc-0.8.35/Forge differential corpus
is a genuinely reusable, citable artifact: an executable Solidity 0.8.35 semantics validated
against the reference compiler, usable by fuzzers, other analyzers, auditing tools, and
alternative compilers — not just this one backend. Burying it inside a compiler repo (whose other
2275 commits are about Yul/EVM lowering and optimization) dilutes and obscures that. The target
spec EVMYulLean is kept standalone for exactly this reason. **→ strongly favors separate.**

**5. Practical mechanics.** Git-dependency friction (pin bumps, occasional cross-repo PRs, two CI
lanes) is real but *already paid* — this project pins `evmyul` and hash-checks a shared-interaction
path dep. Monorepo friction is worse in this case: one repo carrying a Foundry harness + 732 `.sol`
cases + `contest/` alongside a large proof-heavy compiler, with coupled release velocity and a
single CI that must rebuild everything on any change. **→ favors separate; monorepo only if pin
churn ever dominates.**

**6. Third option — head-to-head.**
- *Separate-repo-dependency* (RECOMMENDED): matches the EVMYulLean precedent exactly; clean
  spec-vs-implementation boundary; preserves the standalone artifact; smallest change from today.
- *Monorepo, three clean Lake packages* (source-sem / evm-interaction-or-evmyul-dep / compiler):
  legitimate; buys atomic commits and one CI; the right move **iff** the bridge proof enters
  sustained co-development. But it breaks symmetry with the still-external EVMYulLean and drags the
  corpus/harness into the compiler repo. Keep as the documented fallback.
- *Subfolder-merge (the prototype)*: **worst.** Asymmetric (target stays an external dep while
  source is inlined), the POC doesn't even wire the package, it hides the citable artifact, and it
  couples release velocity — all cost, no proof-level benefit that a dependency edge wouldn't give.

---

## (d) What would change the recommendation

Switch to **monorepo-multi-package** if any of these become true:
1. **A real end-to-end Solidity→EVM theorem enters sustained, simultaneous development** across the
   source spec and the compiler, such that a majority of source-semantics commits must land
   atomically with compiler-proof commits (measure it: if cross-repo pin-bump PRs start
   outnumbering solc-differential PRs in `solid-core-spine`, the boundary is costing more than it
   saves).
2. **EVMYulLean is itself pulled in-tree** — if the *target* spec stops being an external dep and
   moves into the compiler repo, the symmetry argument flips and the source spec should follow.
3. **Version-pin churn becomes the dominant workflow pain** — constant lock-step rev bumps with no
   independent-release value.

Even then, prefer three *clean Lake packages in one repo* over the subfolder-merge, and keep the
differential corpus/Foundry harness in its own package so it doesn't gate compiler CI.
The subfolder-merge does not become the right answer under any condition identified here.

---

## (e) Concrete next steps for the recommended option

1. **Publish the source spec as a standalone git library**, mirroring EVMYulLean. Give
   `solid-core-spine` a stable public root (it already has `SolidCore.lean` / `lean_lib SolidCore`)
   and push to a git remote (e.g. `github.com/danrobinson/Solidus.git`). Keep the name `Solidus`
   for the *library*; note the collision with `evm-compiler`'s internal `EvmCompiler.Solidus`
   namespace and rename one side (recommend the compiler's internal freeze-cone namespace, or
   namespace the library as `SolidCore` throughout its public surface) to avoid confusion.
2. **Resolve the two current deps first.** `solid-core-spine` presently uses a **path** dep
   `require «evm-interaction» from ".."/"evm-interaction"` guarded by
   `scripts/check_shared_interaction_hashes.py`. Before publishing, promote that to a git dep (the
   in-repo comment already says "promote to a git URL later") so the library is clone-and-build
   without sibling checkouts.
3. **The dependency edge, when the end-to-end theorem is built**, added to
   `evm-compiler/lakefile.lean` right beside the existing `evmyul` line:
   ```
   require solidus from git
     "https://github.com/danrobinson/Solidus.git" @ "<pinned-rev>"
   ```
   The full Solidity→EVM correctness theorem then lives **in `evm-compiler`** (the artifact being
   verified), importing `SolidCore` (source spec) and `EvmYul` (target spec) and bridging the
   compiler's existing `rawObjectRun`-based `compile_correct` up to `SolidCore`'s Solidity-source
   semantics.
4. **CI:** keep two lanes. `solid-core-spine` CI stays solc-0.8.35 + Forge differential (its real
   oracle); `evm-compiler` CI pins a `solidus` rev and bumps it deliberately. A scheduled
   "bump-and-build" job in the compiler can surface breakage early without coupling the two release
   cadences.
5. **Retire the subfolder-merge prototype** at `/Users/dan/Projects/solidus` (originals are
   untouched, so nothing is lost), or repurpose it only if step (1)'s monorepo *fallback* is later
   triggered — in which case rebuild it as three real Lake packages, not a file join.

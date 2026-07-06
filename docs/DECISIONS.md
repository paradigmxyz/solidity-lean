# Decisions log (autonomous cleanup run)

One dated entry per non-obvious decision taken while executing `ROADMAP.md`.
The run is fully autonomous; where the phases and implementation notes leave a
choice open, the most conservative behavior-preserving option was taken and
recorded here.

## 2026-07-06 — Phase 1: pinned Keccak is FFI/opaque, keep the pure local spec

`danrobinson/EVMYulLean @ 3c5c44a6` ships Keccak256 as an FFI symbol, not a
pure Lean function:

- `EvmYul/SpongeHash/Keccak256.lean` in the pin is an empty stub (a comment:
  "Use FFI in the meanwhile").
- The actual hash is `@[extern "keccak256"] opaque keccak256 (input : ByteArray)
  (len : USize) : ByteArray` in `EvmYul/FFI/ffi.lean`.

An `opaque`/`@[extern]` function is unusable from this repo's total, purely
computational fuel interpreter: it does not reduce, cannot be `#eval`'d without
native linking, and carries no equational content for future theorems.

Decision (matches ROADMAP Phase 1 specifics fallback, verbatim: "If the pinned
implementation turns out to be `partial`/IO-backed and unusable from a total
interpreter, keep the local pure implementation, rename it to make local-ness
explicit, and add a corpus-checked byte-parity witness against the pinned one —
do not silently keep a shim"):

- Only `EvmYul.UInt256` retargets to the real pinned type (it is a pure,
  reducible `structure ... deriving`, and exposes every named op
  `SharedSemantics.Word` uses).
- The pure Keccak stays, moved out of the `EvmYul.*` namespace into a clearly
  repo-owned module, so nothing masquerades as an upstream shim.
- A byte-parity witness against the pinned FFI keccak is added where the build
  can link it; if native linking of the extern symbol is not available in the
  witness/harness path, that is recorded as a limitation here rather than
  silently skipped.

## 2026-07-06 — Phase 1: reuse the sibling build's prebuilt dependency tree

`../evm-compiler` already has `danrobinson/EVMYulLean @ 3c5c44a6` + its Mathlib
pin built against the exact same toolchain (Lean v4.28.0) this phase moves to.
Rather than a multi-hour from-scratch Mathlib + EVMYulLean build, this repo's
`.lake/packages` is seeded by an APFS copy-on-write clone of the sibling's
prebuilt package tree, and the dependency section of the sibling's
`lake-manifest.json` is reused verbatim (same revs). This is a build-cache
reuse only: `../evm-compiler` is never written to, the `require evmyul from
git ... @ 3c5c44a6` in the lakefile is the real dependency of record, and Lake
remains free to refetch/rebuild from it.

## 2026-07-06 — Phase 1: toolchain-downgrade (4.29.1 → 4.28.0) mechanical fixes

The v4.28.0 downgrade surfaced three purely mechanical, behavior-preserving
breakages. None changes what the interpreter computes; each was fixed without a
new pinned lane because there is no observable-behavior delta.

1. **`alias` is a reserved token in v4.28.0.** The struct field
   `InternalFunctionAliasBinding.alias` and a few local `let`/pattern binders
   named `alias` (Interface/TypeCheck/Checked.lean) no longer parse as bare
   identifiers. Escaped in place as `«alias»` (guillemet identifier) rather than
   renamed, so the field name — and therefore any `Repr`/derive output — is
   byte-identical. `alias?` binders and `"alias"` string literals are distinct
   tokens and were left untouched. No manifest change (the manifest references
   `alias` only in prose/variable names, never the field).

2. **`decreasing_by … omega` over-solves.** In `TypeCheck.lean` one termination
   proof (`checkMemberCallArgs`, ~line 7385) used `all_goals (simp_wf; omega)`;
   under v4.28.0 `simp_wf` already closes some goals, so `omega` errors with
   "No goals to be solved". Changed the lone bare `omega` to `try omega`
   (the file's other 20 termination proofs already used `try omega`).
   Termination proofs are irrelevant to the function's computational content.

3. **`to` is a reserved token in v4.28.0.** The hand-authored `openzeppelin-erc20`
   eval expression in `tests/forge-harness/manifest.json` bound a local
   `let to := 0xbeef` (a transfer-recipient address) and referenced it as
   `Value.word to`; `to` no longer parses as a bare identifier, so the generated
   `interpreter.lean` failed with `unexpected token 'to'` (the sole `lean=exit_1`
   in the first full replay). Alpha-renamed the local binder to `toAddr` in that
   one expression only (3 unique substrings). This is a local-variable rename
   inside a single eval; it changes no assertion and no expectation, and the
   manifest eval count is unchanged (420). The `"to"` strings that name the
   Solidity parameter live in generated AST-importer output, not the manifest,
   and were not touched.

## 2026-07-06 — Phase 1: Keccak byte-parity witness runs and passes

The `lean_exe keccakParity` (native-linked via the pinned `libleanffi`) compares
the repo-owned pure Keccak against the pinned FFI `ffi.KEC` on 11 representative
inputs (empty, real ABI selectors, event-topic signatures, and byte ranges
crossing the 136-byte rate boundary). `lake exe keccakParity` prints
`keccak parity: OK` and exits 0, discharging the roadmap's byte-parity
requirement directly rather than leaving it as an assumption.

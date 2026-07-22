#!/usr/bin/env python3
"""Versioned exclusion register for the divergence contest (design §1).

The register is the contract between the maintainer and entrants: it enumerates
every place solidity-lean INTENTIONALLY does not model Solidity 0.8.35, so that a
rejection or divergence traceable to one of these is OUT_OF_SCOPE, not a
qualifying gap.

Two kinds of entries:

  * SYNTACTIC (§1.1) - decidable by a pure AST scan (node type / member name /
    directive presence). A single hit anywhere in any submitted source => OOS.
    The AST-level entries (assembly, imports, storage layout) REUSE the
    importer's ``EXCLUDED_NODE_TYPES`` table as the single source of truth, so
    the register and the importer can never drift (§7). We import that table
    here rather than re-typing the node-type strings.

  * SEMANTIC (§1.2) - the feature may appear; what is excluded is ASSERTING on
    an observable solidity-lean does not model faithfully (gas amounts, real compiled
    bytecode, create2 predicted addresses, closed-world gas). Detected by the
    feature's AST predicate plus a conservative taint pass (see reject_gate.py).

The register is versioned (``REGISTER_VERSION``, semver) and SHRINKS as gaps are
fixed: an entry is retired by setting ``removed_in_version`` (never deleted), so
historical adjudications stay reproducible. Each submission is judged against the
register in force at its timestamp.
"""

from __future__ import annotations

import importlib.util
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


# v1.2: added X-EXTCALL (external calls unmodeled in v1).
# v1.3: RETIRED X-RETABI (the recursive ABI codec landed: array/struct return
#       values and custom-error revert params are now decoded into solidity-lean's
#       [..]/(..) rendering and compared, so nested-dynamic RETURN/REVERT
#       observables are measured, not excluded) and X-ERRSEL (a colliding revert
#       selector is now resolved to the MODEL-reported error and compared on the
#       byte-faithful selector+args form, exactly as the EVM dispatches revert
#       data — the error NAME was never on-chain-observable, so this can neither
#       fabricate nor mask a divergence). Added the two NARROW residues those
#       broad rows also covered: X-ARGVAL (entry/constructor PARAMETER families
#       the v1 claim arg forms cannot represent/validate) and X-FNVAL
#       (function-typed values in the return/revert channel, which solidity-lean
#       renders via the r:reprStr fallback while the EVM ABI-encodes a word).
# v1.4: RETIRED X-ARGVAL (array and struct ENTRY/CONSTRUCTOR PARAMETERS are now
#       encoded end-to-end: a JSON-list claim arg is validated recursively per
#       element/member, TYPE-DIRECTED ABI-encoded into the EVM calldata
#       (measure._encode_typed — the exact head/tail bytes solc's encoder
#       produces), and rendered as the matching Value.dynamicArray/fixedArray/
#       tuple on the Lean side, so both engines receive the SAME logical call
#       and array/struct-parameter behavior is MEASURED, not excluded) and
#       X-FNVAL (an EXTERNAL function value carries (address, selector) on both
#       sides — the model's Value.externalFunction payload and the EVM's
#       24-byte left-packed ABI word — and both render the canonical
#       `f:<addr>:<sel>` form, so external function values in the return/
#       revert channel are compared byte-faithfully). Added the two narrow
#       residues: X-FNARG (function-typed PARAMETERS — no meaningful function
#       VALUE can be fabricated from a claim — plus per-arg scalar families
#       whose domain the type string cannot bound) and X-INTFNVAL (INTERNAL
#       function values in the return/revert channel, which are per-contract
#       dispatch IDs with no ABI encoding).
# v1.5: RETIRED X-FIXED-EXEC as redundant. Probe evidence (solc 0.8.35,
#       2026-07-22): every form the row's detector fires on — a BinaryOperation
#       or Assignment with a fixed/ufixed operand — is REJECTED by solc at
#       codegen ("UnimplementedFeatureError: Fixed point types not
#       implemented." for `fixed x = 1.5;` / `a + b` / param arithmetic;
#       "Not yet implemented - FixedPointType." for `x == x` / state
#       `x = y;`), so no such program can ever pass the Forge real-behavior
#       gate: a lane-C claim is INVALID by construction, and a lane-S
#       OVER_ACCEPT claim (solc rejects, model accepts) would be a GENUINE
#       soundness gap that an exclusion row must not mask. Forms solc DOES
#       compile — bare declarations (`fixed x;` state/local, `ufixed y;`),
#       `delete x` on a fixed state var, and local decl-init from another
#       fixed local — never triggered the detector in the first place and are
#       modeled: the fixed-point-boundary corpus lane pins both engines
#       agreeing on them (accepted) and on the 9 invalid/ arithmetic forms
#       (rejected). The row therefore excluded nothing real; retired.
REGISTER_VERSION = "1.5.0"

_REPO_ROOT = Path(__file__).resolve().parents[1]


def _load_importer_excluded_node_types() -> dict[str, str]:
    """Import ``EXCLUDED_NODE_TYPES`` from the importer as the single source of
    truth for the AST-level syntactic exclusions.

    We load the module by file path (the ``scripts/`` directory is not a
    package) and read the exact dict the importer's fail-closed guard uses
    (``guard_no_unsupported_nodes``). This is the anti-drift guarantee of §7:
    if the importer starts supporting a node type (e.g. imports), the register
    stops excluding it automatically, with no second edit.
    """
    script = _REPO_ROOT / "scripts" / "solc_ast_to_lean_source.py"
    spec = importlib.util.spec_from_file_location("solc_ast_to_lean_source", script)
    if spec is None or spec.loader is None:  # pragma: no cover - defensive
        raise RuntimeError(f"cannot load importer module from {script}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    excluded = getattr(module, "EXCLUDED_NODE_TYPES", None)
    if not isinstance(excluded, dict):
        raise RuntimeError("importer EXCLUDED_NODE_TYPES missing or not a dict")
    return dict(excluded)


# The importer's canonical excluded-node table. Currently:
#   {'ImportDirective': ..., 'InlineAssembly': ...}
# Yul nodes are excluded by the importer via a ``nodeType.startswith("Yul")``
# rule rather than an explicit table entry; the gate mirrors that rule too.
EXCLUDED_NODE_TYPES: dict[str, str] = _load_importer_excluded_node_types()


def _semver_tuple(v: str) -> tuple[int, ...]:
    """Parse a dotted semver into an int tuple (missing/garbage parts -> 0)."""
    parts: list[int] = []
    for p in str(v).split("."):
        try:
            parts.append(int(p))
        except ValueError:
            parts.append(0)
    return tuple(parts)


def _semver_lt(a: str, b: str) -> bool:
    """True if version ``a`` is strictly less than ``b`` (component-wise)."""
    ta, tb = _semver_tuple(a), _semver_tuple(b)
    n = max(len(ta), len(tb))
    ta += (0,) * (n - len(ta))
    tb += (0,) * (n - len(tb))
    return ta < tb


@dataclass(frozen=True)
class ExclusionEntry:
    """One row of the register (design §1.3)."""

    id: str
    kind: str  # "syntactic" | "semantic"
    detector: str  # name of the predicate implemented in reject_gate.py
    reason: str
    roadmap_ref: str
    since_version: str = "1.0.0"
    removed_in_version: Optional[str] = None
    # For syntactic node-type detectors sourced from the importer, the node
    # types this row is responsible for (populated from EXCLUDED_NODE_TYPES so
    # the two cannot drift). Empty for detectors keyed on member names/options.
    node_types: tuple[str, ...] = field(default_factory=tuple)

    def is_active(self, at_version: Optional[str] = None) -> bool:
        """Is this row in force at register version ``at_version`` (§7 fairness).

        A submission is judged against the register in force at its timestamp, so
        the window is: active iff ``since_version <= at_version`` AND
        (not yet removed OR ``at_version < removed_in_version``). With
        ``at_version is None`` (the live register), a row is active iff it has not
        been removed."""
        if at_version is None:
            return self.removed_in_version is None
        if _semver_lt(at_version, self.since_version):
            return False  # row did not exist yet at at_version
        if self.removed_in_version is not None and \
                not _semver_lt(at_version, self.removed_in_version):
            return False  # row was retired at/before at_version
        return True


# ---------------------------------------------------------------------------
# Syntactic exclusions (§1.1). Detector names map to functions in reject_gate.py
# ---------------------------------------------------------------------------

_SYNTACTIC: list[ExclusionEntry] = [
    ExclusionEntry(
        id="X-ASM",
        kind="syntactic",
        detector="detect_inline_assembly",
        reason=(
            "Inline assembly / Yul is intentionally out of scope; the meaning "
            "is the shared Yul semantics, deferred. Sourced from the importer's "
            "EXCLUDED_NODE_TYPES ('InlineAssembly') plus the Yul* node rule."
        ),
        roadmap_ref="ROADMAP.md:469; solc_ast_to_lean_source.py EXCLUDED_NODE_TYPES",
        node_types=tuple(
            n for n in EXCLUDED_NODE_TYPES if n == "InlineAssembly"
        ),
    ),
    ExclusionEntry(
        id="X-IMPORT",
        kind="syntactic",
        detector="detect_import_directive",
        reason=(
            "Imports / multi-file units are out of scope; flattening is the "
            "intended preprocessing step. Sourced from the importer's "
            "EXCLUDED_NODE_TYPES ('ImportDirective'). Multiple contracts in ONE "
            "flattened source ARE allowed (v1 restricts to single-contract via "
            "V1-MULTI, §3.3)."
        ),
        roadmap_ref="ROADMAP.md:470; solc_ast_to_lean_source.py EXCLUDED_NODE_TYPES",
        node_types=tuple(
            n for n in EXCLUDED_NODE_TYPES if n == "ImportDirective"
        ),
    ),
    ExclusionEntry(
        id="X-GASLEFT",
        kind="syntactic",
        detector="detect_gasleft",
        reason=(
            "gasleft() is modeled as a resource query answered ambiently, not "
            "real gas metering; its value is not a faithful observable."
        ),
        roadmap_ref="ROADMAP.md:467/473",
    ),
    ExclusionEntry(
        id="X-MSIZE",
        kind="syntactic",
        detector="detect_msize",
        reason=(
            "msize has no memory-size model; only reachable via assembly (also "
            "caught by X-ASM). Retained for defense-in-depth."
        ),
        roadmap_ref="mission brief",
    ),
    ExclusionEntry(
        id="X-STORAGELAYOUT",
        kind="syntactic",
        detector="detect_storage_layout_specifier",
        reason=(
            "`layout at N` storage-layout specifier is fail-closed at import; "
            "it is assembly-observed and out of scope."
        ),
        roadmap_ref="solc_ast_to_lean_source.py guard",
    ),
    ExclusionEntry(
        id="X-FIXED-EXEC",
        kind="syntactic",
        detector="detect_executable_fixed_point",
        # RETIRED in 1.5.0 as REDUNDANT — see the v1.5 probe-evidence note on
        # REGISTER_VERSION above: solc rejects (at codegen, so Forge can never
        # PASS) every form this detector fires on, making a lane-C claim
        # INVALID without this row, while excluding a lane-S over-accept here
        # would mask a genuine gap; the solc-compilable fixed-point forms
        # (bare declarations, delete, decl-init) never triggered the detector
        # and are measured by the fixed-point-boundary lane.
        removed_in_version="1.5.0",
        reason=(
            "Executable fixed/ufixed arithmetic is ALSO rejected by solc "
            "(fixed-point-boundary lane confirms both agree); a divergence here "
            "is impossible, so a submission asserting one is OOS by construction."
        ),
        roadmap_ref="docs/rational-constants-audit.md; fixed-point-boundary lane",
    ),
    ExclusionEntry(
        id="X-EXTCALL",
        kind="syntactic",
        detector="detect_external_call",
        since_version="1.2.0",
        reason=(
            "External calls are not modeled in the v1 single-contract path: the "
            "responder-free interpreter answers every external call with a fixed "
            "default (the call fails / returns empty) rather than executing a "
            "callee or a real EVM interaction. So a low-level call to an EOA "
            "(EVM: success-empty), a precompile (EVM: real output), a high-level "
            "call to another contract, `this.f()`, or a try/catch over an "
            "external call all diverge for a NON-semantic reason. CONTRACT "
            "CREATION is EXPLICITLY out of scope too, in every form: `new C()`, "
            "`new C{salt: s}()`, `new C{value: v}()` — i.e. CREATE and CREATE2. "
            "A creation executes a DEPLOYMENT SUB-CONTEXT (the callee's "
            "constructor) and its observable outcome (success -> the created/"
            "CREATE2 address; failure -> revert on a constructor revert or an "
            "already-occupied address) requires the v2 responder to model; v1 "
            "does not model it or derive the address. (In-memory allocations "
            "`new T[](n)` / `new bytes(n)` are NOT creations and stay in scope.) "
            "Out of scope until the v2 reflective responder lands (design §3, "
            "multi_contract.py seam); retire this row then."
        ),
        roadmap_ref="competition-design.md §3.2/§3.3; multi_contract.py",
    ),
    ExclusionEntry(
        id="X-RETABI",
        kind="syntactic",
        # Entry-function-return-type specific, so it is checked by the adjudicator
        # (which knows the entry function), NOT by a whole-source gate detector.
        # The gate skips register rows whose detector is absent from its table.
        detector="adjudicator:entry_return_type",
        since_version="1.2.0",
        # RETIRED in 1.3.0: the recursive ABI head/tail codec landed
        # (observable._decode_abi_values + measure.struct_definitions), so
        # array/struct/nested-dynamic RETURN values and custom-error REVERT
        # params now decode into the exact [..]/(..) normal form solidity-lean
        # renders and are MEASURED + COMPARED, not excluded. The two narrow
        # residues this broad row also covered live on as X-ARGVAL (parameter
        # arg-form representation) and X-FNVAL (function-typed values).
        removed_in_version="1.3.0",
        reason=(
            "An entry function PARAMETER or RETURN type is outside the faithfully "
            "encodable/comparable ABI subset. The harness represents args as direct "
            "CoreValues to Solidus and as ABI calldata to the EVM, and decodes EVM "
            "return bytes back to Solidus's value rendering, EXACTLY for scalars "
            "(int/uint/bool/address/enum/contract/bytesN), dynamic bytes/string, "
            "and flat tuples (multiple returns) of those. ARRAY (`T[]`, `T[N]`) and "
            "STRUCT types are not yet encoded/decoded to match Solidus's "
            "`[..]`/`(..)` form on either side, so using them would raise a spurious "
            "divergence. The SAME subset bounds the custom-error REVERT channel: a "
            "custom error with an array/struct/tuple/function-typed param decodes "
            "differently on each side for identical behavior, so such a revert is "
            "also out of scope (adjudicator, revert channel). Out of scope until the "
            "recursive ABI codec lands; restructure to use scalars/bytes/string "
            "meanwhile."
        ),
        roadmap_ref="competition-design.md §3.4; observable._decode_abi_values",
    ),
    ExclusionEntry(
        id="X-ERRSEL",
        kind="syntactic",
        # Adjudicator-checked (revert channel): needs the measured revert selector.
        detector="adjudicator:revert_selector",
        since_version="1.2.0",
        # RETIRED in 1.3.0: a colliding measured selector is now resolved to the
        # MODEL-reported error definition and compared on the byte-faithful
        # selector+args form — exactly how the EVM dispatches revert data
        # (solc 0.8.35 verified: it rejects colliding errors within one contract
        # but ACCEPTS a file-level/cross-contract collision, so such programs
        # are legal and must be adjudicated). Because the error NAME is not
        # on-chain-observable, name-label resolution can neither fabricate a
        # divergence the bytes do not show nor mask one they do (see
        # adjudicate.py, ambiguous-selector resolution).
        removed_in_version="1.3.0",
        reason=(
            "The measured revert's 4-byte selector is defined by TWO OR MORE "
            "distinctly-named custom errors in the submission — a 4-byte selector "
            "collision. solc rejects colliding errors within one contract but NOT "
            "across separate contracts or a file-level error, so a submission can "
            "plant a second error (e.g. a brute-forced `E94430()` colliding with "
            "the entry's `E82926()`) that a last-wins selector map resolves to "
            "instead of the actually-reverted one. The on-chain revert bytes are "
            "IDENTICAL for both (same selector, same args) and no caller can tell "
            "them apart, so the custom-error NAME is not a faithful observable and "
            "a name mismatch would fabricate a wrong-revert SOUNDNESS_GAP. Such a "
            "revert is out of scope; give the errors distinct 4-byte selectors."
        ),
        roadmap_ref="competition-design.md §3.4; measure.error_definitions",
    ),
    ExclusionEntry(
        id="X-ARGVAL",
        kind="syntactic",
        # Entry/constructor-PARAMETER specific: checked by the adjudicator, which
        # knows the entry signature. The gate skips rows without a gate detector.
        detector="adjudicator:entry_param_type",
        since_version="1.3.0",
        # RETIRED in 1.4.0: array/struct parameters are encoded end-to-end
        # (JSON-list claim args, recursively domain-validated; type-directed
        # ABI calldata on the EVM side; Value.dynamicArray/fixedArray/tuple on
        # the Lean side — the same logical call on both engines), so they are
        # measured, not excluded. The narrow residues live on as X-FNARG.
        removed_in_version="1.4.0",
        reason=(
            "An entry-function or constructor PARAMETER type is outside what the "
            "v1 claim.json arg forms can represent AND domain-validate: the arg "
            "forms are word / {int} / {bytes} / bool, so an array-, struct-, "
            "tuple- or function-typed parameter cannot be expressed, and a "
            "word-family scalar whose legal domain cannot be bounded from the "
            "type string alone (bytesN with N<32, fixed/ufixed, an enum whose "
            "member count is unresolvable) cannot be validated — an unvalidated "
            "arg would let a submitter feed the two engines different logical "
            "calls and fabricate a divergence. This is the narrow PARAMETER "
            "residue of the retired X-RETABI (the RETURN/REVERT channel is now "
            "fully decoded+compared); restructure the entry to scalar/bytes/"
            "string parameters meanwhile."
        ),
        roadmap_ref="adjudicate._arg_domain_error; observable.render_lean_arg",
    ),
    ExclusionEntry(
        id="X-FNVAL",
        kind="syntactic",
        # Return/revert-channel specific: checked by the adjudicator.
        detector="adjudicator:entry_return_type",
        since_version="1.3.0",
        # RETIRED in 1.4.0: an EXTERNAL function value is comparable — the
        # model's Value.externalFunction carries the same (address, selector)
        # pair the EVM ABI left-packs into its 24-byte word, and both sides now
        # render the canonical `f:<addr>:<sel>` form. The genuinely
        # non-ABI-encodable residue (INTERNAL function values, unresolvable
        # structs) lives on as X-INTFNVAL.
        removed_in_version="1.4.0",
        reason=(
            "A FUNCTION-typed value (or a struct/array containing one) in the "
            "entry RETURN or custom-error REVERT channel: solidity-lean renders an "
            "internal/external function value via the r:reprStr fallback while "
            "the EVM ABI-encodes it as a static word, so identical behavior "
            "would compare unequal (a fabricated wrong-value/wrong-revert). "
            "Also covers a struct type the harness cannot resolve to member "
            "types. The narrow RETURN/REVERT residue of the retired X-RETABI; "
            "every other ABI type (scalars, bytes/string, arrays, structs, "
            "arbitrarily nested) is now decoded and compared."
        ),
        roadmap_ref="observable._decode_abi_values; adjudicate._comparable_channel_type",
    ),
    ExclusionEntry(
        id="X-FNARG",
        kind="syntactic",
        # Entry/constructor-PARAMETER specific: checked by the adjudicator,
        # which knows the entry/constructor signature. The gate skips register
        # rows whose detector is absent from its table.
        detector="adjudicator:entry_param_type",
        since_version="1.4.0",
        reason=(
            "The narrow PARAMETER residue of the retired X-ARGVAL (arrays and "
            "structs — arbitrarily nested — are now encoded end-to-end and "
            "measured). Out of scope remain: (a) a FUNCTION-typed entry/"
            "constructor parameter, in any nesting — an external function VALUE "
            "is an (address, selector) pair with no callee behind it in the v1 "
            "responder-free world, so no meaningful function argument can be "
            "fabricated from a claim, and an internal function value is a "
            "per-contract dispatch ID that is not ABI calldata at all; (b) a "
            "struct parameter the harness cannot resolve to member types, or a "
            "bare tuple typeString; and (c) per-arg, a word-family scalar leaf "
            "whose legal domain cannot be bounded from the type string alone "
            "(bytesN with N<32, fixed/ufixed, an enum whose member count is "
            "unresolvable) — an unvalidated leaf would let a submitter feed the "
            "two engines different logical calls and fabricate a divergence. "
            "Restructure such parameters to scalar/bytes/string/array/struct "
            "shapes of bounded leaves meanwhile."
        ),
        roadmap_ref=("adjudicate._encodable_param_type / _arg_domain_error; "
                     "measure._encode_typed; observable.render_lean_arg"),
    ),
    ExclusionEntry(
        id="X-INTFNVAL",
        kind="syntactic",
        # Return/revert-channel specific: checked by the adjudicator.
        detector="adjudicator:entry_return_type",
        since_version="1.4.0",
        reason=(
            "The narrow RETURN/REVERT residue of the retired X-FNVAL (an "
            "EXTERNAL function value now compares: both engines render the "
            "canonical `f:<addr>:<sel>` form from the (address, selector) pair "
            "the ABI word packs). Out of scope remain INTERNAL function-typed "
            "values (or a struct/array containing one) in the entry RETURN or "
            "custom-error REVERT channel — an internal function value is a "
            "per-contract dispatch ID with NO ABI encoding (solc itself rejects "
            "internal function types in external signatures, so this row is "
            "defense-in-depth against typeString drift) — plus a struct type "
            "the harness cannot resolve to member types (undecodable)."
        ),
        roadmap_ref=("adjudicate._comparable_channel_type(external_fn_ok=True); "
                     "observable.render_word_for_type"),
    ),
]


# ---------------------------------------------------------------------------
# Semantic exclusions (§1.2). Feature-presence is not a hit; use-as-observable
# (a value derived from the excluded quantity reaching an asserted observable)
# is. The taint pass lives in reject_gate.py.
# ---------------------------------------------------------------------------

_SEMANTIC: list[ExclusionEntry] = [
    ExclusionEntry(
        id="SEM-GAS",
        kind="semantic",
        detector="detect_gas_observable",
        reason=(
            "A value derived from gasleft()/tx.gasprice/a .gas-option effect "
            "flowing into an assertion or the observed return. Gas is not "
            "metered; any gas-quantity observable is definitionally "
            "divergent-but-OOS."
        ),
        roadmap_ref="ROADMAP.md:473",
    ),
    ExclusionEntry(
        id="SEM-CODE",
        kind="semantic",
        detector="detect_creationcode_observable",
        reason=(
            "An observable depending on real compiled bytecode - "
            "type(C).creationCode/.runtimeCode, address(c).code, .codehash of "
            "created code. solidity-lean's initCode is source-canonical "
            "(len||name||args), not EVM bytecode."
        ),
        roadmap_ref="ROADMAP.md:468",
    ),
    ExclusionEntry(
        id="SEM-ADDR",
        kind="semantic",
        detector="detect_create2_address_observable",
        reason=(
            "A create2 predicted address (or any address depending on init "
            "bytecode) flowing to an assertion/observed return. create2 address "
            "= keccak(0xff||deployer||salt||keccak(initcode)); solidity-lean lacks "
            "real initcode (G22). Non-salted `new` addresses ARE in scope."
        ),
        roadmap_ref="ROADMAP.md:468; G22",
    ),
    ExclusionEntry(
        id="SEM-ENV",
        kind="semantic",
        detector="detect_env_observable",
        since_version="1.1.0",
        reason=(
            "An observable derived from an UNPINNABLE env fact - blockhash(n) / "
            "blobhash(i) - flowing into an assertion or observed return. The "
            "canonical block/tx/self env (number, timestamp, chainid, basefee, "
            "coinbase, prevrandao, gaslimit, msg.sender, tx.origin, "
            "address(this)) IS pinned identically on both engines (contest/"
            "env.py = Foundry's real defaults) and therefore compared, not "
            "excluded; but solidity-lean has no historical block/blob hashes, so a "
            "blockhash/blobhash observable would be a spurious divergence."
        ),
        roadmap_ref="competition-design-review.md E-1; contest/env.py",
    ),
    ExclusionEntry(
        id="SEM-CLOSEDGAS",
        kind="semantic",
        detector="detect_closed_world_gas_observable",
        reason=(
            "Closed-world gas metering / OOG as an observable, or a "
            "send/transfer 2300-stipend-driven success/revert difference. "
            "solidity-lean does not meter gas or the stipend."
        ),
        roadmap_ref="ROADMAP.md:473",
    ),
]


def all_entries(include_retired: bool = False,
                at_version: Optional[str] = None) -> list[ExclusionEntry]:
    entries = _SYNTACTIC + _SEMANTIC
    if include_retired:
        return list(entries)
    return [e for e in entries if e.is_active(at_version)]


def syntactic_entries(at_version: Optional[str] = None) -> list[ExclusionEntry]:
    return [e for e in _SYNTACTIC if e.is_active(at_version)]


def semantic_entries(at_version: Optional[str] = None) -> list[ExclusionEntry]:
    return [e for e in _SEMANTIC if e.is_active(at_version)]


def entry_by_id(entry_id: str) -> Optional[ExclusionEntry]:
    for e in all_entries(include_retired=True):
        if e.id == entry_id:
            return e
    return None


def register_summary() -> dict:
    return {
        "register_version": REGISTER_VERSION,
        "importer_excluded_node_types": EXCLUDED_NODE_TYPES,
        "syntactic": [e.id for e in syntactic_entries()],
        "semantic": [e.id for e in semantic_entries()],
    }


if __name__ == "__main__":
    import json

    print(json.dumps(register_summary(), indent=2))

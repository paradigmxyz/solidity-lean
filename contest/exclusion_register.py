#!/usr/bin/env python3
"""Versioned exclusion register for the divergence contest (design §1).

The register is the contract between the maintainer and entrants: it enumerates
every place Solidus INTENTIONALLY does not model Solidity 0.8.35, so that a
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
    an observable Solidus does not model faithfully (gas amounts, real compiled
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


REGISTER_VERSION = "1.1.0"  # v1.1: added SEM-ENV (env-observable exclusion)

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
        """A row is active unless it was retired at/ before ``at_version``.

        (v1 uses simple presence; full semver-window comparison is a v1.x
        refinement noted in §7. Since REGISTER_VERSION never rewinds within a
        contest, ``removed_in_version is None`` is the operative predicate.)
        """
        return self.removed_in_version is None


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
        reason=(
            "Executable fixed/ufixed arithmetic is ALSO rejected by solc "
            "(fixed-point-boundary lane confirms both agree); a divergence here "
            "is impossible, so a submission asserting one is OOS by construction."
        ),
        roadmap_ref="docs/rational-constants-audit.md; fixed-point-boundary lane",
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
            "created code. Solidus's initCode is source-canonical "
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
            "= keccak(0xff||deployer||salt||keccak(initcode)); Solidus lacks "
            "real initcode (G22). Non-salted `new` addresses ARE in scope."
        ),
        roadmap_ref="ROADMAP.md:468; G22",
    ),
    ExclusionEntry(
        id="SEM-ENV",
        kind="semantic",
        detector="detect_env_observable",
        reason=(
            "An observable derived from an UNPINNABLE env fact - blockhash(n) / "
            "blobhash(i) - flowing into an assertion or observed return. The "
            "canonical block/tx/self env (number, timestamp, chainid, basefee, "
            "coinbase, prevrandao, gaslimit, msg.sender, tx.origin, "
            "address(this)) IS pinned identically on both engines (contest/"
            "env.py = Foundry's real defaults) and therefore compared, not "
            "excluded; but Solidus has no historical block/blob hashes, so a "
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
            "Solidus does not meter gas or the stipend."
        ),
        roadmap_ref="ROADMAP.md:473",
    ),
]


def all_entries(include_retired: bool = False) -> list[ExclusionEntry]:
    entries = _SYNTACTIC + _SEMANTIC
    if include_retired:
        return list(entries)
    return [e for e in entries if e.is_active()]


def syntactic_entries() -> list[ExclusionEntry]:
    return [e for e in _SYNTACTIC if e.is_active()]


def semantic_entries() -> list[ExclusionEntry]:
    return [e for e in _SEMANTIC if e.is_active()]


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

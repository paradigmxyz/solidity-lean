#!/usr/bin/env python3
"""The ONE canonical repro fingerprinter for the known-gap registry.

WHY THIS MODULE EXISTS (registry redesign, 2026-07)
---------------------------------------------------
The registry in ``contest/known_gaps.py`` used to key its entries on HAND-WRITTEN
human-readable slugs (``"nested-tuple-LHS"``, ``"ec-cmp"``, ...). The live
adjudicator, however, computes its fingerprints from live engine output
(``adjudicate.coverage_fingerprint`` / ``soundness_fingerprint``), so a
hand-authored key could NEVER string-match a real submission's computed
fingerprint: those registry rows were INERT — they implied dedup coverage that
did not exist, and could silently drift from reality forever.

THE INVARIANT THIS MODULE GUARANTEES
------------------------------------
A registry key is never hand-authored. Every registry entry carries its REPRO
(the Solidity source(s) that exhibit the gap), and the entry's fingerprint is
DERIVED from that repro by this one canonical function:

    fingerprint = repro_fingerprint(lane, delta_class, repro_sources)

The stored fingerprints (``contest/known_gap_fingerprints.json``) are generated
by ``python3 -m contest.known_gaps --rebuild`` and VERIFIED by the registry
invariant test in ``contest/run_samples.py``: for every entry with a repro,
stored-fingerprint == repro_fingerprint(entry.repro). Hand-editing a key, or
changing this fingerprinter, makes that test fail loudly instead of a registry
row silently going inert.

WHAT THE FINGERPRINT IS
-----------------------
``fp1|<lane>|<delta_class>|<ast-mode>|<hash16>`` where ``hash16`` is a
structural hash of the pinned-solc AST(s) of the repro, canonicalized to be:

  * DETERMINISTIC: a pure function of the AST — no timestamps, paths, solc
    node ids, or dict ordering leak in (keys are visited sorted; node ids are
    alpha-renamed, below).
  * ALPHA-INVARIANT: identifier NAMES are dropped; declarations and the
    references to them are numbered by first appearance in a canonical
    traversal, so renaming every variable/function/contract yields the SAME
    fingerprint while ``a - b`` vs ``b - a`` (different reference order) stay
    DIFFERENT.
  * ORDER-INVARIANT where order is irrelevant: top-level source-unit members
    (pragma / contract order) and the multi-file combination are sorted by
    their own structural hash. Statement/expression/member order inside a
    contract is PRESERVED (state-variable order affects storage layout;
    statement order affects behavior) — collapsing it could over-match two
    genuinely different programs, which is the one direction dedup must not
    err in.
  * VARIATION-ROBUST: whitespace, comments, file names, file order, and
    identifier spelling do not change the fingerprint.
  * DISTINCTNESS-PRESERVING: literals, operators, types, mutability, member
    names, and structure are all part of the hash, so distinct divergences get
    distinct fingerprints (two different programs colliding requires a sha256
    collision).

SOUNDNESS DIRECTION (must never wrongly auto-deny credit)
---------------------------------------------------------
This fingerprint deliberately identifies "the same PROGRAM up to renaming/
reordering", not "the same ROOT CAUSE". Matching is therefore heavily
UNDER-matching: a genuinely novel find can never hash-collide into a known
entry (short of breaking sha256), so an exact match means the submission is a
copy/re-skin of a published repro — the safe direction. Same-root-cause dedup
with a DIFFERENT program is decided by the authoritative fix-time replay
(``contest/dedup_replay.py``), never by this hint layer.

AST modes: an over-accept repro is solc-REJECTED by definition, so it has no
analyzed AST; those hash the parse-only AST (mode ``parse``, name-based
references since parse-only nodes carry no referencedDeclaration). Everything
else hashes the analyzed AST (mode ``full``). The mode is part of the
fingerprint string so the two families can never collide.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Optional

FINGERPRINT_SCHEME = "fp1"

# Node types whose solc `id` can be the target of a `referencedDeclaration`;
# visiting one registers its id in the alpha-renaming map (first-visit order),
# so `return a;` vs `return b;` differ even though both names are dropped.
_DECL_NODE_TYPES = frozenset({
    "VariableDeclaration", "FunctionDefinition", "ContractDefinition",
    "StructDefinition", "EnumDefinition", "EnumValue", "ErrorDefinition",
    "EventDefinition", "ModifierDefinition", "UserDefinedValueTypeDefinition",
    "ImportDirective", "SourceUnit",
})

# Scalar attributes that are SEMANTIC and safe to include (no names/ids/paths).
_SALIENT_ATTRS = (
    "operator", "kind", "value", "hexValue", "memberName",
    "visibility", "stateMutability", "storageLocation", "mutability",
    "virtual", "abstract", "anonymous", "indexed", "constant",
    "isConstructor", "global", "payable", "prefix", "isInlineArray",
    "number",  # Literal subdenomination-free numeric spelling
)

# Node types where `name` IS the semantics (a type name), not an identifier.
_NAME_IS_SEMANTIC = frozenset({"ElementaryTypeName"})

# Child fields visited before the (sorted) rest, so declarations register in
# the alpha-renaming map before the code that references them.
_KEY_PRIORITY = ("parameters", "returnParameters", "typeName", "declarations",
                 "baseContracts")


def _is_node(v: Any) -> bool:
    return isinstance(v, dict) and "nodeType" in v


def _h(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8", "surrogatepass")).hexdigest()


def _canon(node: Any, refmap: Optional[dict[int, int]]) -> str:
    """Structural hash of one AST node (recursive).

    ``refmap`` is the alpha-renaming map (solc declaration id -> canonical
    index, first-visit order). Pass ``None`` for the PRELIMINARY pass used only
    to order source-unit members (refs hash as a placeholder there, so the
    ordering itself cannot depend on ids)."""
    if isinstance(node, list):
        return _h("[" + ",".join(_canon(x, refmap) for x in node) + "]")
    if not _is_node(node):
        # scalar leftovers inside kept structures (e.g. FunctionCall "names")
        return _h("s:" + json.dumps(node, sort_keys=True, default=str))

    nt = node["nodeType"]
    parts: list[str] = ["n:" + nt]

    # register declarations in first-visit order (final pass only)
    if refmap is not None and nt in _DECL_NODE_TYPES and isinstance(
            node.get("id"), int):
        refmap.setdefault(node["id"], len(refmap))

    for attr in _SALIENT_ATTRS:
        if attr in node and not isinstance(node[attr], (dict, list)):
            parts.append(f"{attr}={node[attr]!r}")
    if nt in _NAME_IS_SEMANTIC and node.get("name") is not None:
        parts.append(f"tname={node['name']!r}")

    # canonical reference identity (alpha-invariant, distinctness-preserving)
    rd = node.get("referencedDeclaration")
    if isinstance(rd, int):
        if refmap is None:
            parts.append("ref=?")
        elif rd < 0:
            # solc builtins (msg, require, ...) have stable negative magic ids
            parts.append(f"ref=builtin:{rd}")
        else:
            parts.append(f"ref={refmap.setdefault(rd, len(refmap))}")
    elif nt in ("Identifier", "IdentifierPath", "UserDefinedTypeName") \
            and node.get("name") is not None:
        # parse-only AST (over-accept repros) has no referencedDeclaration:
        # fall back to the spelled name (deterministic; mode `parse` is a
        # separate fingerprint family so it can never collide with `full`).
        parts.append(f"name={node['name']!r}")
    if node.get("names"):  # named call arguments: order/name is semantic
        parts.append(f"argnames={list(node['names'])!r}")

    # children: dict keys in a fixed canonical order (dict-order invariant);
    # list order PRESERVED except SourceUnit members, sorted by a preliminary
    # ref-free hash. Declaration-bearing fields come FIRST so the alpha-
    # renaming map registers declarations before their uses: with plain sorted
    # order, "body" < "parameters" and refs would be numbered by first USE,
    # collapsing `x - y` with `y - x` (an over-match — the forbidden
    # direction).
    keys = [k for k in _KEY_PRIORITY if k in node] + \
           [k for k in sorted(node.keys()) if k not in _KEY_PRIORITY]
    for key in keys:
        val = node[key]
        if _is_node(val):
            parts.append(f"{key}:{_canon(val, refmap)}")
        elif isinstance(val, list) and any(_is_node(x) for x in val):
            if nt == "SourceUnit" and key == "nodes":
                order = sorted(val, key=lambda x: _canon(x, None))
                parts.append(
                    f"{key}:[{','.join(_canon(x, refmap) for x in order)}]")
            else:
                parts.append(
                    f"{key}:[{','.join(_canon(x, refmap) for x in val)}]")
    return _h("|".join(parts))


def canonical_ast_hash(asts: list[dict]) -> str:
    """Combined structural hash of one repro's solc AST(s). Multi-file repros
    combine ORDER-INDEPENDENTLY (per-file hashes sorted)."""
    per_file: list[str] = []
    for ast in asts:
        refmap: dict[int, int] = {}
        per_file.append(_canon(ast, refmap))
    return _h("+".join(sorted(per_file)))


def source_ast_hash(sources: list[Path], solc: Optional[str] = None,
                    ) -> tuple[str, str]:
    """(hash, mode) for a list of .sol sources under the pinned solc.

    mode ``full`` = analyzed AST (referencedDeclaration-based alpha renaming);
    mode ``parse`` = parse-only fallback for solc-REJECTED sources (over-accept
    repros). The mode is embedded in the fingerprint so the families are
    disjoint.

    CWD-INDEPENDENT by construction: the derivation hands solc ABSOLUTE source
    paths and runs with the sources' COMMON PARENT directory as the working
    directory (restored afterwards). solc's standard-json import callback
    allows only "." — the process cwd — so a repro whose files import a
    sibling (`import "./Other.sol";`, legal in corpus lanes; submissions are
    single-flattened via X-IMPORT) resolves identically no matter where the
    caller was invoked from: the registry invariant test and the exact-copy
    auto-match must both work from ANY cwd (including tmp-dir copies)."""
    import os
    from . import reject_gate as gate
    if solc is None:
        from . import harness_bridge as hb
        solc = hb.DEFAULT_SOLC
    repo_root = Path(__file__).resolve().parents[1]
    abs_sources = [Path(p).resolve() if Path(p).is_absolute()
                   else (repo_root / p).resolve() for p in sources]
    parents = {p.parent for p in abs_sources}
    workdir = (os.path.commonpath([str(d) for d in parents])
               if parents else str(repo_root))
    prev_cwd = os.getcwd()
    try:
        os.chdir(workdir)
        try:
            src_asts = gate.get_source_asts(abs_sources, solc)
            mode = "full"
        except Exception:
            src_asts = gate.get_source_asts_parse_only(abs_sources, solc)
            mode = "parse"
    finally:
        os.chdir(prev_cwd)
    return canonical_ast_hash([sa.ast for sa in src_asts]), mode


def repro_fingerprint(lane: str, delta_class: str, sources: list[Path],
                      solc: Optional[str] = None) -> str:
    """THE canonical fingerprint of a repro: derived, never hand-authored.

    ``lane`` is "C" | "S"; ``delta_class`` is the adjudicator-derived delta
    family (lane C: ``over_reject`` / ``missing_feature``; lane S:
    ``wrong-value`` / ``wrong-panic`` / ``wrong-revert`` / ``wrong-state`` /
    ``revert-vs-success`` / ``over-accept``)."""
    digest, mode = source_ast_hash(sources, solc)
    return f"{FINGERPRINT_SCHEME}|{lane}|{delta_class}|{mode}|{digest[:16]}"


def _main(argv: Optional[list[str]] = None) -> int:
    import argparse
    p = argparse.ArgumentParser(
        description="Compute the canonical repro fingerprint of .sol sources")
    p.add_argument("sources", type=Path, nargs="+")
    p.add_argument("--lane", required=True, choices=["C", "S"])
    p.add_argument("--delta", required=True,
                   help="delta class (over_reject / wrong-value / ...)")
    p.add_argument("--solc", default=None)
    args = p.parse_args(argv)
    print(repro_fingerprint(args.lane, args.delta, args.sources, args.solc))
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())

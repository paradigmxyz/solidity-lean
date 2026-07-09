#!/usr/bin/env python3
"""Minimality / shrink advisory (design §6.3).

A qualifying submission should reduce to the smallest program exhibiting the
divergence — one entry function, minimal callees, no dead code — so a genuine
gap is not buried in a haystack (and so two haystack variants of one root cause
do not both score). A full shrink check re-runs the pipeline after deleting each
top-level declaration; this module is the cheap STATIC proxy: a call-graph
reachability pass over the solc AST that flags functions in the entry contract
(and its bases) that are NOT reachable from the entry function.

It is ADVISORY: the adjudicator annotates the report with the result but does not
change the verdict. The signal (``unreachable_functions``) is what a maintainer
uses to ask for a shrink or to down-weight a cluster.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Optional

from . import reject_gate as gate


# Functions that are legitimately present without being called from the entry:
# the constructor, receive/fallback, and compiler-synthesised public-state getters
# (which have no body). We never flag these as dead.
def _is_exempt(fn: dict[str, Any]) -> bool:
    kind = fn.get("kind")
    if kind in ("constructor", "receive", "fallback"):
        return True
    # public state-variable getter: implicit, no body.
    if fn.get("implemented") is False and fn.get("body") is None:
        return True
    return False


def _referenced_fn_ids(node: Any) -> set[int]:
    """Every function/modifier id referenced anywhere in ``node`` via
    ``referencedDeclaration`` (FunctionCall callees, MemberAccess, Identifiers,
    modifier invocations, super/`this` calls)."""
    ids: set[int] = set()
    for n in gate.iter_nodes(node):
        ref = n.get("referencedDeclaration")
        if isinstance(ref, int):
            ids.add(ref)
    return ids


def minimality_report(sources: list[Path], entry_contract: str,
                      entry_function: str, solc: str) -> dict[str, Any]:
    """Return {minimal, unreachable_functions, note}. Best-effort and fail-open:
    any analysis error yields ``minimal=None`` (unknown), never an exception."""
    try:
        asts = gate.get_source_asts(sources, solc=solc)
    except Exception as exc:  # pragma: no cover - defensive
        return {"minimal": None, "unreachable_functions": [],
                "note": f"minimality analysis skipped: {exc}"}

    # Index every ContractDefinition by id, and locate the entry contract.
    contracts_by_id: dict[int, dict[str, Any]] = {}
    entry_node: Optional[dict[str, Any]] = None
    for src in asts:
        for n in gate.iter_nodes(src.ast):
            if n.get("nodeType") != "ContractDefinition":
                continue
            cid = n.get("id")
            if isinstance(cid, int):
                contracts_by_id[cid] = n
            if n.get("name") == entry_contract:
                entry_node = n
    if entry_node is None:
        return {"minimal": None, "unreachable_functions": [],
                "note": f"entry contract {entry_contract} not found"}

    # The entry contract's own functions plus every base in its linearised chain.
    chain_ids = [i for i in (entry_node.get("linearizedBaseContracts") or [])
                 if isinstance(i, int)] or [entry_node.get("id")]
    funcs_by_id: dict[int, dict[str, Any]] = {}
    for cid in chain_ids:
        c = contracts_by_id.get(cid)
        if not c:
            continue
        for item in c.get("nodes", []):
            if item.get("nodeType") == "FunctionDefinition" and isinstance(item.get("id"), int):
                funcs_by_id[item["id"]] = item

    # Find the entry function (by name, preferring the most-derived contract).
    entry_ids = [fid for fid, f in funcs_by_id.items()
                 if f.get("name") == entry_function]
    if not entry_ids:
        return {"minimal": None, "unreachable_functions": [],
                "note": f"entry function {entry_function} not found"}

    # BFS the call graph from the entry function over referencedDeclaration ids.
    reachable: set[int] = set(entry_ids)
    frontier = list(entry_ids)
    while frontier:
        fid = frontier.pop()
        fn = funcs_by_id.get(fid)
        if fn is None:
            continue
        for ref in _referenced_fn_ids(fn):
            if ref in funcs_by_id and ref not in reachable:
                reachable.add(ref)
                frontier.append(ref)

    unreachable = sorted(
        fn.get("name") or f"<fn#{fid}>"
        for fid, fn in funcs_by_id.items()
        if fid not in reachable and not _is_exempt(fn))

    minimal = len(unreachable) == 0
    note = ("minimal: every function is reachable from the entry" if minimal
            else f"{len(unreachable)} function(s) unreachable from the entry "
                 f"(dead code / haystack): consider shrinking")
    return {"minimal": minimal, "unreachable_functions": unreachable, "note": note}

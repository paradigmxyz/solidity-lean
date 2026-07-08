#!/usr/bin/env python3
"""Reject gate - whole-submission AST scan (design §2).

Runs AFTER solc has produced the analyzed AST for ALL submitted sources and
BEFORE Solidus import. It consumes the same solc JSON AST the importer consumes
(pinned solc 0.8.35), so it sees exactly what Solidus would see.

It scans EVERY ContractDefinition in EVERY SourceUnit of the submission - entry
contract, every callee, every library, every base - not just the named entry
point. (An adversary hides gasleft() in a callee to force a fake value
divergence; whole-submission scanning is the counter, §6.1a.)

Output: a structured verdict, either

    OUT_OF_SCOPE { register_version, hits: [{id, source, contract, node_src,
                   reason, taint_path?}] }
or
    PASS { register_version }

Syntactic detectors (§1.1) are an exact one-pass predicate over
nodeType/memberName/directive presence. Semantic detectors (§1.2) are a
two-part check: (a) the feature appears, AND (b) a CONSERVATIVE intra-source
taint pass shows a value derived from the excluded quantity reaching an OBSERVED
position (an assertion comparand or the entry call's return/revert/event).

PRECISION LIMIT (documented, §1.2 / §8): the taint pass is deliberately
conservative and errs toward OOS. v1 approximates "reaches an assertion" as
"the excluded quantity appears anywhere in a function that also performs a
require/assert/return/emit, OR is compared/returned within the same source" -
i.e. a coarse whole-source reachability rather than precise def-use dataflow.
A false OOS costs one entrant a resubmission with the observable removed; a
false PASS would let an adversary bank a fake divergence, so the bias is correct.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Iterable, Optional

from . import env as cenv
from . import exclusion_register as reg


_REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOLC = "/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35"


def _load_importer():
    script = _REPO_ROOT / "scripts" / "solc_ast_to_lean_source.py"
    spec = importlib.util.spec_from_file_location("solc_ast_to_lean_source", script)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


_IMPORTER = _load_importer()


# ---------------------------------------------------------------------------
# AST walking helpers
# ---------------------------------------------------------------------------

def iter_nodes(node: Any):
    """Yield every dict node in the AST (depth-first)."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from iter_nodes(value)
    elif isinstance(node, list):
        for item in node:
            yield from iter_nodes(item)


def node_src(node: dict[str, Any]) -> str:
    return str(node.get("src", "?"))


def type_string(node: dict[str, Any]) -> str:
    td = node.get("typeDescriptions")
    if isinstance(td, dict):
        return str(td.get("typeString") or "")
    return ""


def enclosing_contract_name(ast: dict[str, Any], target: dict[str, Any]) -> str:
    """Best-effort name of the ContractDefinition enclosing ``target``."""
    stack: list[str] = []

    def walk(node: Any, current: Optional[str]) -> Optional[str]:
        if isinstance(node, dict):
            if node is target:
                return current
            if node.get("nodeType") == "ContractDefinition":
                current = str(node.get("name") or "?")
            for value in node.values():
                found = walk(value, current)
                if found is not None:
                    return found
        elif isinstance(node, list):
            for item in node:
                found = walk(item, current)
                if found is not None:
                    return found
        return None

    return walk(ast, None) or "?"


# ---------------------------------------------------------------------------
# Verdict types
# ---------------------------------------------------------------------------

@dataclass
class Hit:
    id: str
    source: str
    contract: str
    node_src: str
    reason: str
    taint_path: Optional[str] = None

    def to_dict(self) -> dict[str, Any]:
        d = {
            "id": self.id,
            "source": self.source,
            "contract": self.contract,
            "node_src": self.node_src,
            "reason": self.reason,
        }
        if self.taint_path is not None:
            d["taint_path"] = self.taint_path
        return d


@dataclass
class GateVerdict:
    verdict: str  # "OUT_OF_SCOPE" | "PASS"
    register_version: str
    hits: list[Hit] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "verdict": self.verdict,
            "register_version": self.register_version,
        }
        if self.hits:
            d["hits"] = [h.to_dict() for h in self.hits]
        return d

    @property
    def is_pass(self) -> bool:
        return self.verdict == "PASS"


# ---------------------------------------------------------------------------
# A per-source scan context
# ---------------------------------------------------------------------------

@dataclass
class SourceAst:
    source: str  # file name / key
    ast: dict[str, Any]


# ===========================================================================
# SYNTACTIC detectors (§1.1). Each returns a list of Hit for one source AST.
# ===========================================================================

def _yul_node_types(node_type: str) -> bool:
    return node_type.startswith("Yul")


def detect_inline_assembly(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    hits = []
    for node in iter_nodes(src.ast):
        nt = node.get("nodeType")
        if not isinstance(nt, str):
            continue
        if nt == "InlineAssembly" or _yul_node_types(nt):
            hits.append(Hit(entry.id, src.source,
                            enclosing_contract_name(src.ast, node),
                            node_src(node), entry.reason))
    return hits


def detect_import_directive(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    hits = []
    for node in iter_nodes(src.ast):
        if node.get("nodeType") == "ImportDirective":
            hits.append(Hit(entry.id, src.source,
                            enclosing_contract_name(src.ast, node),
                            node_src(node), entry.reason))
    return hits


def _callee_name(node: dict[str, Any]) -> Optional[str]:
    """The called identifier name for a FunctionCall, if any."""
    if node.get("nodeType") != "FunctionCall":
        return None
    callee = node.get("expression")
    if isinstance(callee, dict) and callee.get("nodeType") == "Identifier":
        return callee.get("name")
    return None


def detect_gasleft(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    hits = []
    for node in iter_nodes(src.ast):
        nt = node.get("nodeType")
        if nt == "FunctionCall" and _callee_name(node) == "gasleft":
            hits.append(Hit(entry.id, src.source,
                            enclosing_contract_name(src.ast, node),
                            node_src(node), entry.reason))
        elif nt == "MemberAccess" and node.get("memberName") == "gasleft":
            hits.append(Hit(entry.id, src.source,
                            enclosing_contract_name(src.ast, node),
                            node_src(node), entry.reason))
        elif nt == "Identifier" and node.get("name") == "gasleft":
            hits.append(Hit(entry.id, src.source,
                            enclosing_contract_name(src.ast, node),
                            node_src(node), entry.reason))
    return hits


def detect_msize(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    # msize is only reachable via assembly (caught by X-ASM). Defense-in-depth:
    # any Yul identifier literally named "msize".
    hits = []
    for node in iter_nodes(src.ast):
        if node.get("nodeType", "").startswith("Yul") and node.get("name") == "msize":
            hits.append(Hit(entry.id, src.source,
                            enclosing_contract_name(src.ast, node),
                            node_src(node), entry.reason))
    return hits


def detect_storage_layout_specifier(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    hits = []
    for node in iter_nodes(src.ast):
        nt = node.get("nodeType")
        if nt in ("StorageLayoutSpecifier",) or "storageLayout" in node:
            hits.append(Hit(entry.id, src.source,
                            enclosing_contract_name(src.ast, node),
                            node_src(node), entry.reason))
    return hits


def detect_executable_fixed_point(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    hits = []
    for node in iter_nodes(src.ast):
        nt = node.get("nodeType")
        if nt not in ("BinaryOperation", "Assignment"):
            continue
        for side in ("leftExpression", "rightExpression",
                     "leftHandSide", "rightHandSide"):
            operand = node.get(side)
            if isinstance(operand, dict):
                ts = type_string(operand)
                if ts.startswith("fixed") or ts.startswith("ufixed"):
                    hits.append(Hit(entry.id, src.source,
                                    enclosing_contract_name(src.ast, node),
                                    node_src(node), entry.reason))
                    break
    return hits


# ===========================================================================
# SEMANTIC detectors (§1.2). Feature-presence + conservative taint-to-observable.
# ===========================================================================

# Names that syntactically identify an ASSERTED / OBSERVED position: a Forge
# test's assertion comparands, a require/assert condition, an entry return, or an
# emitted event. If an excluded quantity textually reaches any of these within
# the same function, we conservatively call it observed.
_ASSERT_CALLEES = {
    "assertEq", "assertTrue", "assertFalse", "assertGt", "assertLt",
    "assertGe", "assertLe", "assertEqUint", "assertNotEq", "assertApproxEqAbs",
    "require", "assert",
}


def _find_functions(ast: dict[str, Any]) -> Iterable[dict[str, Any]]:
    for node in iter_nodes(ast):
        if node.get("nodeType") == "FunctionDefinition":
            yield node


def _subtree_contains(node: Any, predicate: Callable[[dict], bool]) -> bool:
    for n in iter_nodes(node):
        if predicate(n):
            return True
    return False


def _function_has_observed_position(fn: dict[str, Any]) -> bool:
    """True if the function body contains an assertion, a return with an
    expression, or an emit - i.e. a position the harness would observe."""
    for n in iter_nodes(fn.get("body")):
        nt = n.get("nodeType")
        if nt == "FunctionCall" and _callee_name(n) in _ASSERT_CALLEES:
            return True
        if nt == "Return" and n.get("expression") is not None:
            return True
        if nt == "EmitStatement":
            return True
    return False


def _tainted_predicate(names_or_members: dict[str, Any]) -> Callable[[dict], bool]:
    """Build a predicate matching an excluded-quantity source expression."""
    ident_names = names_or_members.get("identifiers", set())
    member_names = names_or_members.get("members", set())

    def pred(n: dict[str, Any]) -> bool:
        nt = n.get("nodeType")
        if nt == "Identifier" and n.get("name") in ident_names:
            return True
        if nt == "FunctionCall" and _callee_name(n) in ident_names:
            return True
        if nt == "MemberAccess" and n.get("memberName") in member_names:
            return True
        return False

    return pred


def _semantic_taint_scan(entry: reg.ExclusionEntry, src: SourceAst,
                         spec: dict[str, Any]) -> list[Hit]:
    """Generic semantic detector: for every function whose body BOTH mentions
    the excluded quantity AND has an observed position (§1.2 conservative
    reachability), emit an OOS hit with a taint path."""
    pred = _tainted_predicate(spec)
    hits: list[Hit] = []
    for fn in _find_functions(src.ast):
        body = fn.get("body")
        if body is None:
            continue
        # (a) feature appears in this function
        source_node = None
        for n in iter_nodes(body):
            if pred(n):
                source_node = n
                break
        if source_node is None:
            continue
        # (b) an observed position exists in the same function (conservative)
        if not _function_has_observed_position(fn):
            continue
        fn_name = fn.get("name") or "<anon>"
        taint = (f"{spec['label']} at {node_src(source_node)} reaches an "
                 f"observed position (assert/return/emit) in function "
                 f"'{fn_name}'")
        hits.append(Hit(entry.id, src.source,
                        enclosing_contract_name(src.ast, fn),
                        node_src(source_node), entry.reason, taint_path=taint))
    return hits


def detect_gas_observable(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    return _semantic_taint_scan(entry, src, {
        "label": "gas quantity (gasleft/tx.gasprice)",
        "identifiers": {"gasleft"},
        "members": {"gasleft", "gasprice"},
    })


def detect_creationcode_observable(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    return _semantic_taint_scan(entry, src, {
        "label": "compiled-bytecode quantity (creationCode/runtimeCode/code/codehash)",
        "identifiers": set(),
        "members": {"creationCode", "runtimeCode", "code", "codehash"},
    })


def detect_create2_address_observable(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    """create2 predicted address as observable. A salted `new C{salt:...}()`
    whose resulting address is observed. Conservative: any function that uses a
    `salt:` call option (FunctionCallOptions with name 'salt') and has an
    observed position."""
    hits: list[Hit] = []
    for fn in _find_functions(src.ast):
        body = fn.get("body")
        if body is None:
            continue
        salt_node = None
        for n in iter_nodes(body):
            if n.get("nodeType") == "FunctionCallOptions":
                names = n.get("names")
                if isinstance(names, list) and "salt" in names:
                    salt_node = n
                    break
        if salt_node is None:
            continue
        if not _function_has_observed_position(fn):
            continue
        fn_name = fn.get("name") or "<anon>"
        taint = (f"salted create2 at {node_src(salt_node)} whose address "
                 f"reaches an observed position in function '{fn_name}'")
        hits.append(Hit(entry.id, src.source,
                        enclosing_contract_name(src.ast, fn),
                        node_src(salt_node), entry.reason, taint_path=taint))
    return hits


def detect_env_observable(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    """UNPINNABLE env fact as an observable (review E-1 / P1 env register entry).

    The canonical env (block.number/timestamp/chainid/basefee/coinbase/
    prevrandao/gaslimit, msg.sender, tx.origin, address(this)) IS pinned on both
    engines (see contest/env.py) and therefore compared, not excluded. What
    stays OUT_OF_SCOPE is an observable derived from an env fact Solidus cannot
    mirror: ``blockhash(n)`` / ``blobhash(i)`` (Solidus has no historical block
    or blob hashes unless the harness pins them), which would otherwise become a
    spurious SOUNDNESS_GAP. Conservative taint: the builtin appears in a function
    that also has an observed position."""
    return _semantic_taint_scan(entry, src, {
        "label": "unpinnable env fact (blockhash/blobhash)",
        "identifiers": {"blockhash", "blobhash"},
        "members": {"blockhash", "blobhash"},
    })


def detect_closed_world_gas_observable(entry: reg.ExclusionEntry, src: SourceAst) -> list[Hit]:
    """send/transfer stipend-driven success/revert, or gas-option effect as an
    observable. Conservative: a `.transfer(`/`.send(` member call, or a `gas:`
    call option, in a function with an observed position."""
    hits: list[Hit] = []
    for fn in _find_functions(src.ast):
        body = fn.get("body")
        if body is None:
            continue
        flagged = None
        for n in iter_nodes(body):
            nt = n.get("nodeType")
            if nt == "MemberAccess" and n.get("memberName") in ("transfer", "send"):
                # only .transfer/.send on an address value (stipend semantics)
                if "address" in type_string(n.get("expression", {}) or {}):
                    flagged = n
                    break
            if nt == "FunctionCallOptions":
                names = n.get("names")
                if isinstance(names, list) and "gas" in names:
                    flagged = n
                    break
        if flagged is None:
            continue
        if not _function_has_observed_position(fn):
            continue
        fn_name = fn.get("name") or "<anon>"
        taint = (f"closed-world gas/stipend effect at {node_src(flagged)} "
                 f"reaches an observed position in function '{fn_name}'")
        hits.append(Hit(entry.id, src.source,
                        enclosing_contract_name(src.ast, fn),
                        node_src(flagged), entry.reason, taint_path=taint))
    return hits


# ===========================================================================
# V1-MULTI temporary guard (§3.3): single-contract only. Reject a submission
# with >1 non-library ContractDefinition that are mutually call-reachable. In
# v1 the test contract is NOT part of the submission src/; we only look at the
# submitted sources' non-library, non-interface, non-abstract contracts.
# ===========================================================================

def detect_v1_multi(sources: list[SourceAst]) -> list[Hit]:
    concrete: list[tuple[SourceAst, dict[str, Any]]] = []
    for src in sources:
        for node in iter_nodes(src.ast):
            if node.get("nodeType") != "ContractDefinition":
                continue
            if node.get("contractKind") != "contract":
                continue  # skip library / interface
            if node.get("abstract"):
                continue
            concrete.append((src, node))
    if len(concrete) <= 1:
        return []
    # v1: any 2+ concrete deployable contracts trigger the guard. (A precise
    # mutual-call-reachability analysis is the v2 refinement; the conservative
    # v1 rule rejects all multi-concrete-contract submissions - see seam in
    # multi_contract.py.)
    names = ", ".join(f"{n.get('name')}@{src.source}" for src, n in concrete)
    reason = ("v1 ships single-contract only (design §3.3): the reflective "
              "multi-contract responder is a v2 feature. Submission has "
              f"{len(concrete)} concrete contracts: {names}.")
    hits = []
    for src, n in concrete:
        hits.append(Hit("V1-MULTI", src.source, str(n.get("name") or "?"),
                        node_src(n), reason))
    return hits


# ===========================================================================
# Detector dispatch table (name -> callable)
# ===========================================================================

_SYNTACTIC_DETECTORS: dict[str, Callable[[reg.ExclusionEntry, SourceAst], list[Hit]]] = {
    "detect_inline_assembly": detect_inline_assembly,
    "detect_import_directive": detect_import_directive,
    "detect_gasleft": detect_gasleft,
    "detect_msize": detect_msize,
    "detect_storage_layout_specifier": detect_storage_layout_specifier,
    "detect_executable_fixed_point": detect_executable_fixed_point,
}

_SEMANTIC_DETECTORS: dict[str, Callable[[reg.ExclusionEntry, SourceAst], list[Hit]]] = {
    "detect_gas_observable": detect_gas_observable,
    "detect_creationcode_observable": detect_creationcode_observable,
    "detect_create2_address_observable": detect_create2_address_observable,
    "detect_closed_world_gas_observable": detect_closed_world_gas_observable,
    "detect_env_observable": detect_env_observable,
}


# ===========================================================================
# TEST-FILE cheatcode scan (review P0 #3). The submission's TEST is NOT a
# source Solidus imports, but it drives what the EVM measures. A test using a
# state/oracle-forging cheatcode (vm.store/mockCall/ffi/etch/...) can fabricate
# a divergence Solidus (run from a clean env) can never reproduce. Policy
# (contest/env.py): DEFAULT-DENY every vm.*/hevm cheatcode except the
# env-pinning/setup whitelist, whose literal effects are MIRRORED into the
# Solidus env. Returns (banned_hits, overrides, unmirrorable_hits).
# ===========================================================================

def _literal_int(node: Any) -> Optional[int]:
    """Extract an integer from a Literal / simple address wrapper, else None."""
    if not isinstance(node, dict):
        return None
    nt = node.get("nodeType")
    if nt == "Literal":
        val = node.get("value")
        kind = node.get("kind")
        if kind == "bool":
            return 1 if val in ("true", True) else 0
        if val is None:
            hv = node.get("hexValue")
            return int(hv, 16) if hv else None
        try:
            return int(str(val), 0) if str(val).startswith("0x") else int(str(val))
        except ValueError:
            return None
    # address(<literal>) / uint160(<literal>) / bytes32(<literal>) wrappers
    if nt == "FunctionCall":
        args = node.get("arguments") or []
        if len(args) == 1:
            return _literal_int(args[0])
    return None


def _vm_call_name(node: dict[str, Any]) -> Optional[str]:
    """If ``node`` is a `vm.<member>(...)` / `hevm.<member>(...)` /
    `console.<member>(...)` call, return the member name."""
    if node.get("nodeType") != "FunctionCall":
        return None
    callee = node.get("expression")
    if not isinstance(callee, dict) or callee.get("nodeType") != "MemberAccess":
        return None
    base = callee.get("expression")
    if not isinstance(base, dict) or base.get("nodeType") != "Identifier":
        return None
    if base.get("name") not in ("vm", "hevm", "console", "console2"):
        return None
    return callee.get("memberName")


@dataclass
class CheatcodeScan:
    banned: list[Hit] = field(default_factory=list)
    unmirrorable: list[Hit] = field(default_factory=list)
    overrides: "cenv.EnvOverrides" = field(default_factory=lambda: cenv.EnvOverrides())

    @property
    def rejected(self) -> bool:
        return bool(self.banned or self.unmirrorable)


def scan_test_cheatcodes(test_asts: list[SourceAst]) -> CheatcodeScan:
    scan = CheatcodeScan()
    for src in test_asts:
        base_call = None
        for node in iter_nodes(src.ast):
            name = _vm_call_name(node)
            if name is None:
                continue
            # console.* logging is a harmless observ-ability no-op.
            call_base = node.get("expression", {}).get("expression", {})
            if isinstance(call_base, dict) and call_base.get("name") in ("console", "console2"):
                continue
            if name in cenv.CHEATCODE_IGNORE:
                continue
            if name not in cenv.CHEATCODE_ALLOW:
                scan.banned.append(Hit(
                    "CHEAT-DENY", src.source,
                    enclosing_contract_name(src.ast, node), node_src(node),
                    f"banned cheatcode vm.{name} (default-deny; not on the "
                    f"env-pinning whitelist {sorted(cenv.CHEATCODE_ALLOW)})"))
                continue
            # Whitelisted: mirror its literal effect into the env overrides.
            field = cenv.CHEATCODE_ALLOW[name]
            args = node.get("arguments") or []
            if field == "_noop":
                continue
            if field == "_deal":
                if len(args) == 2:
                    a, amt = _literal_int(args[0]), _literal_int(args[1])
                    if a is not None and amt is not None:
                        scan.overrides.deals.append((a, amt))
                        continue
                scan.unmirrorable.append(Hit(
                    "CHEAT-UNMIRROR", src.source,
                    enclosing_contract_name(src.ast, node), node_src(node),
                    f"vm.{name} with non-literal args cannot be mirrored into "
                    "the Solidus env"))
                continue
            v = _literal_int(args[0]) if args else None
            if v is None:
                scan.unmirrorable.append(Hit(
                    "CHEAT-UNMIRROR", src.source,
                    enclosing_contract_name(src.ast, node), node_src(node),
                    f"vm.{name} with a non-literal argument cannot be mirrored "
                    "into the Solidus env (v1 requires a literal)"))
                continue
            if field == "_sender":
                scan.overrides.sender = v
            else:
                setattr(scan.overrides, field, v)
    return scan



# ===========================================================================
# Public entry points
# ===========================================================================

def multi_source_asts(report_files: list[Path], all_files: list[Path],
                      solc: str = DEFAULT_SOLC) -> list[SourceAst]:
    """Compile ``all_files`` together (so relative imports resolve) and return
    the ASTs of ``report_files``. Used for TEST files, which import ``../src/*``
    and therefore cannot be compiled in isolation (review P0 #3 cheatcode scan).
    """
    import json as _json
    import subprocess as _sp

    request = {
        "language": "Solidity",
        "sources": {p.resolve().as_posix(): {"content": p.read_text()}
                    for p in all_files},
        "settings": {"outputSelection": {"*": {"": ["ast"]}}},
    }
    completed = _sp.run([solc, "--standard-json"], input=_json.dumps(request),
                        text=True, stdout=_sp.PIPE, stderr=_sp.PIPE, check=False)
    try:
        output = _json.loads(completed.stdout)
    except _json.JSONDecodeError:
        return []
    sources = output.get("sources")
    if not isinstance(sources, dict):
        return []
    out: list[SourceAst] = []
    for p in report_files:
        key = p.resolve().as_posix()
        entry = sources.get(key)
        if isinstance(entry, dict) and isinstance(entry.get("ast"), dict):
            out.append(SourceAst(source=key, ast=entry["ast"]))
    return out


def get_source_asts(sources: list[Path], solc: str = DEFAULT_SOLC) -> list[SourceAst]:
    """Get the analyzed solc AST for each source (reuses the importer's
    ``run_solc_ast``, so it is byte-for-byte what Solidus would import)."""
    out: list[SourceAst] = []
    for path in sources:
        name, ast = _IMPORTER.run_solc_ast(solc, path)
        out.append(SourceAst(source=name, ast=ast))
    return out


def run_gate_on_asts(sources: list[SourceAst],
                     enforce_v1_multi: bool = True) -> GateVerdict:
    hits: list[Hit] = []
    for entry in reg.syntactic_entries():
        detector = _SYNTACTIC_DETECTORS.get(entry.detector)
        if detector is None:
            continue
        for src in sources:
            hits.extend(detector(entry, src))
    for entry in reg.semantic_entries():
        detector = _SEMANTIC_DETECTORS.get(entry.detector)
        if detector is None:
            continue
        for src in sources:
            hits.extend(detector(entry, src))
    if enforce_v1_multi:
        hits.extend(detect_v1_multi(sources))

    if hits:
        return GateVerdict("OUT_OF_SCOPE", reg.REGISTER_VERSION, hits)
    return GateVerdict("PASS", reg.REGISTER_VERSION)


def run_gate(sources: list[Path], solc: str = DEFAULT_SOLC,
             enforce_v1_multi: bool = True) -> GateVerdict:
    asts = get_source_asts(sources, solc=solc)
    return run_gate_on_asts(asts, enforce_v1_multi=enforce_v1_multi)


def _main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Run the contest reject gate over .sol sources")
    p.add_argument("sources", nargs="+", type=Path)
    p.add_argument("--solc", default=DEFAULT_SOLC)
    p.add_argument("--no-v1-multi", action="store_true",
                   help="disable the temporary single-contract V1-MULTI guard")
    args = p.parse_args(argv)
    verdict = run_gate(args.sources, solc=args.solc,
                       enforce_v1_multi=not args.no_v1_multi)
    print(json.dumps(verdict.to_dict(), indent=2))
    return 0 if verdict.is_pass else 3


if __name__ == "__main__":
    raise SystemExit(_main())

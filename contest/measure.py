#!/usr/bin/env python3
"""Measure the EVM-side observable from an ACTUAL Forge run (review P0 #1).

The v1 adjudicator diffed solidity-lean against ``claim.declared_observable`` - an
entrant-controlled string (review O-1, CONTEST-BREAKING). This module instead
MEASURES the EVM observable: it generates a tiny Foundry harness that deploys the
entry contract, replays the whitelisted env cheatcodes (so the EVM env == the
canonical pinned env, contest/env.py), performs the ENTRY call by raw calldata,
and dumps the raw ``(ok, ret-bytes, self, origin)`` to a file. The adjudicator
decodes those bytes (observable.evm_observable) into the same normal form solidity-lean
renders and diffs the two. ``declared_observable`` is now only a sanity hint.

Reuses the harness's pinned solc/forge invocation conventions
(scripts/run_forge_interpreter_harness.py); does not reinvent them.
"""

from __future__ import annotations

import re
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional

from . import env as cenv
from . import reject_gate as gate


# The standard Foundry cheatcode address = address(uint160(uint256(keccak256(
# "hevm cheat code")))). We reference it by that expression in the harness.
_CHEAT_EXPR = "address(uint160(uint256(keccak256(\"hevm cheat code\"))))"


@dataclass
class EntrySig:
    selector: str            # 4-byte hex, no 0x
    param_types: list[str]
    return_types: list[str]
    source_file: Path
    contract: str
    # Number of FunctionDefinitions in the entry contract sharing this name
    # (release audit): with OVERLOADS (>1) the by-name entry is ambiguous — the
    # harness would pick one overload for the EVM calldata while the Lean
    # by-name dispatch could resolve another, feeding the engines two different
    # logical calls (a fabricated divergence). The adjudicator rejects >1.
    overload_count: int = 1


@dataclass
class Measurement:
    ok: bool                 # entry call succeeded (True) vs reverted (False)
    ret_hex: str             # raw return (ok) or revert (not ok) bytes, 0x-hex
    self_addr: int           # deployed entry-contract address (mirror -> solidity-lean)
    origin: int
    raw: str                 # the raw dumped line, for evidence
    events: str = ""         # rendered events section (§3.4 component 4)
    storage: str = ""        # rendered observed-storage section (component 5)
    # True when the CONSTRUCTOR reverted: the deploy itself failed, the entry
    # call never ran, and ret_hex carries the constructor's revert data
    # (Error(string) / Panic / custom error / empty). self_addr is then the
    # PREDICTED create address (what the contract's address would have been),
    # so address(this) inside the model's constructor still mirrors the EVM.
    deploy_reverted: bool = False


# ---------------------------------------------------------------------------
# AST extraction of the entry function signature.
# ---------------------------------------------------------------------------

def entry_signature(source: Path, contract: str, function: str,
                    solc: str) -> Optional[EntrySig]:
    _name, ast = gate._IMPORTER.run_solc_ast(solc, source)
    for node in gate.iter_nodes(ast):
        if node.get("nodeType") != "ContractDefinition" or node.get("name") != contract:
            continue
        matches = [item for item in node.get("nodes", [])
                   if item.get("nodeType") == "FunctionDefinition"
                   and item.get("name") == function]
        for item in matches:
            selector = item.get("functionSelector")
            if not selector:
                return None
            params = [_param_type(p) for p in
                      item.get("parameters", {}).get("parameters", [])]
            returns = [_param_type(p) for p in
                       item.get("returnParameters", {}).get("parameters", [])]
            return EntrySig(selector, params, returns, source, contract,
                            overload_count=len(matches))
    return None


def _param_type(p: dict[str, Any]) -> str:
    td = p.get("typeDescriptions") or {}
    return str(td.get("typeString") or "")


def error_definitions(
        source: Path, solc: str
) -> tuple[dict[str, tuple[str, list[str]]], set[str]]:
    """Map each user-defined error's 4-byte selector (8 lowercase hex, no 0x) to
    ``(name, [param_type, ...])`` from the compiled AST, so the EVM side can
    decode a custom-error revert into the ``custom:<Name>:...`` normal form.

    Uses solc's own ``errorSelector`` on each ``ErrorDefinition`` node (no keccak
    dependency); errors without a selector are skipped.

    Returns ``(defs, ambiguous)`` where ``ambiguous`` is the set of selectors
    defined by TWO OR MORE distinctly-named errors — a 4-byte selector collision.
    solc rejects colliding errors WITHIN one contract, but NOT across separate
    contracts or a file-level error, so a submission can plant a second error
    (e.g. a brute-forced ``E94430()`` colliding with the entry's ``E82926()``)
    whose name a last-wins selector map would resolve to instead of the actually-
    reverted one. The on-chain revert bytes are IDENTICAL for both (same selector,
    same args), so a name mismatch would fabricate a wrong-revert SOUNDNESS_GAP;
    the caller routes an ambiguous-selector revert to REJECTED_OOS."""
    out: dict[str, tuple[str, list[str]]] = {}
    ambiguous: set[str] = set()
    try:
        _name, ast = gate._IMPORTER.run_solc_ast(solc, source)
    except Exception:
        return out, ambiguous
    for node in gate.iter_nodes(ast):
        if node.get("nodeType") != "ErrorDefinition":
            continue
        sel = node.get("errorSelector")
        name = node.get("name")
        if not sel or not name:
            continue
        sel = str(sel).lower()
        types = [_param_type(p) for p in
                 node.get("parameters", {}).get("parameters", [])]
        prior = out.get(sel)
        if prior is not None and prior[0] != str(name):
            ambiguous.add(sel)   # same selector, different error name -> collision
        out[sel] = (str(name), types)
    return out, ambiguous


def error_definition_list(
        source: Path, solc: str) -> list[tuple[str, str, list[str]]]:
    """EVERY user-defined error as ``(selector, name, [param_type, ...])``,
    INCLUDING all parties to a 4-byte selector collision (which the last-wins
    map of :func:`error_definitions` cannot represent). The adjudicator uses
    this to resolve an ambiguous (colliding) measured revert selector to the
    error the MODEL reports — sound because the on-chain revert bytes carry
    only selector+args, so the name label never changes what is compared."""
    out: list[tuple[str, str, list[str]]] = []
    try:
        _name, ast = gate._IMPORTER.run_solc_ast(solc, source)
    except Exception:
        return out
    for node in gate.iter_nodes(ast):
        if node.get("nodeType") != "ErrorDefinition":
            continue
        sel = node.get("errorSelector")
        name = node.get("name")
        if not sel or not name:
            continue
        types = [_param_type(p) for p in
                 node.get("parameters", {}).get("parameters", [])]
        out.append((str(sel).lower(), str(name), types))
    return out


def struct_definitions(source: Path, solc: str) -> dict[str, list[str]]:
    """Map each StructDefinition's canonical name (e.g. ``C.S``, or ``S`` for a
    file-level struct) to its member typeStrings, so the recursive ABI decoder
    (observable._decode_abi_values) can decode struct-typed return values and
    custom-error params into solidity-lean's ``(..)`` tuple rendering."""
    out: dict[str, list[str]] = {}
    try:
        _name, ast = gate._IMPORTER.run_solc_ast(solc, source)
    except Exception:
        return out
    for node in gate.iter_nodes(ast):
        if node.get("nodeType") != "StructDefinition":
            continue
        canonical = node.get("canonicalName") or node.get("name")
        if not canonical:
            continue
        out[str(canonical)] = [_param_type(m) for m in (node.get("members") or [])]
    return out


def constructor_param_types(source: Path, contract: str,
                            solc: str) -> list[str]:
    """The parameter typeStrings of ``contract``'s constructor (``[]`` if it has
    none / an implicit no-arg constructor), so the adjudicator can validate
    constructor_args the same way it validates entry args."""
    try:
        _name, ast = gate._IMPORTER.run_solc_ast(solc, source)
    except Exception:
        return []
    for node in gate.iter_nodes(ast):
        if node.get("nodeType") != "ContractDefinition" or \
                node.get("name") != contract:
            continue
        for item in node.get("nodes", []):
            if item.get("nodeType") == "FunctionDefinition" and \
                    item.get("kind") == "constructor":
                return [_param_type(p) for p in
                        item.get("parameters", {}).get("parameters", [])]
    return []


def enum_member_counts(source: Path, solc: str) -> dict[str, int]:
    """Map each enum's canonical name (e.g. ``C.E``) to its MEMBER COUNT, so the
    adjudicator can validate that an enum-typed entry arg is a legal member.

    solc's external ABI decoder reverts on an out-of-range enum input, so an arg
    >= the member count is not a legal high-level call (it would fabricate a
    divergence). Enums without a resolvable name are skipped."""
    out: dict[str, int] = {}
    try:
        _name, ast = gate._IMPORTER.run_solc_ast(solc, source)
    except Exception:
        return out
    for node in gate.iter_nodes(ast):
        if node.get("nodeType") != "EnumDefinition":
            continue
        canonical = node.get("canonicalName") or node.get("name")
        members = node.get("members") or []
        if canonical and members:
            out[str(canonical)] = len(members)
    return out


# ---------------------------------------------------------------------------
# Python-side ABI encoding of the entry args (from claim.json) into calldata.
# Scalar arg forms: word / int / bytes / bool. Register >= 1.4.0 additionally
# encodes ARRAY (`T[]` / `T[N]`, arbitrarily nested) and STRUCT parameters
# from JSON lists, TYPE-DIRECTED (the parameter typeString from the compiled
# AST decides static-inline vs offset+tail layout), so array/struct entry and
# constructor args reach the EVM as the exact head/tail encoding solc's own
# ABI produces (X-ARGVAL retired). The recursive layout mirrors the decoder
# (observable._decode_tuple), sharing its type predicates so the two cannot
# drift. Static args go in the head; dynamic values get an offset+tail.
# ---------------------------------------------------------------------------

def _encode_arg(arg: Any) -> tuple[bool, bytes]:
    """Return (is_dynamic, encoded). Static -> 32 bytes; dynamic -> the tail."""
    if isinstance(arg, bool):
        return False, (1 if arg else 0).to_bytes(32, "big")
    if isinstance(arg, int):
        return False, (arg % (1 << 256)).to_bytes(32, "big")
    if isinstance(arg, dict):
        if "word" in arg:
            return False, (int(arg["word"]) % (1 << 256)).to_bytes(32, "big")
        if "int" in arg:
            return False, (int(arg["int"]) % (1 << 256)).to_bytes(32, "big")
        if "bytes" in arg:
            h = str(arg["bytes"])
            h = h[2:] if h.startswith("0x") else h
            data = bytes.fromhex(h)
            length = len(data).to_bytes(32, "big")
            padded = data + b"\x00" * ((32 - len(data) % 32) % 32)
            return True, length + padded
    raise ValueError(f"unsupported entry arg form for calldata: {arg!r}")


def _arg_component_word(v: Any) -> int:
    """The unsigned word an external-function arg COMPONENT denotes (a bare
    non-negative int or the {"word": n} form); raises on any other shape —
    the adjudicator's domain validation rejects those before encoding."""
    if isinstance(v, bool):
        raise ValueError(f"external function arg component must be an "
                         f"unsigned integer, got {v!r}")
    if isinstance(v, int):
        return v
    if isinstance(v, dict) and "word" in v:
        return int(v["word"])
    raise ValueError(f"external function arg component must be an unsigned "
                     f"int / {{\"word\": n}}, got {v!r}")


def _encode_typed(arg: Any, t: str,
                  structs: Optional[dict[str, list[str]]]) -> tuple[bool, bytes]:
    """TYPE-DIRECTED encode of one arg for parameter type ``t``.

    Returns ``(is_dynamic, encoded)`` where ``encoded`` is the value's full
    encoding (for a dynamic value: the tail bytes the offset will point at; for
    a static value: the inline head bytes — 32 for a scalar, the concatenated
    parts for a static fixed array / static struct). Shape errors raise
    ValueError; the adjudicator's arg-domain validation rejects them as
    REJECT_MALFORMED before any encoding runs (fabrication fence)."""
    from . import observable as obs  # local import; observable does not import us
    ct = obs._clean_type(t)
    arr = obs._array_elem(ct)
    if arr is not None:
        elem, n = arr
        if not isinstance(arg, list):
            raise ValueError(f"array parameter {t!r} requires a JSON list arg, "
                             f"got {arg!r}")
        if n is None:  # dynamic T[]: length word + tuple-encoded elements
            body = len(arg).to_bytes(32, "big") + \
                _encode_tuple_typed(arg, [elem] * len(arg), structs)
            return True, body
        if len(arg) != n:
            raise ValueError(f"fixed array {t!r} requires exactly {n} elements, "
                             f"got {len(arg)}")
        body = _encode_tuple_typed(arg, [elem] * n, structs)
        return obs._is_dynamic_type(ct, structs), body
    if ct.startswith("function"):
        # EXTERNAL function-typed parameter (register >= 1.6.0, X-FNARG
        # retired): the [address, selector] claim arg is ABI-encoded as the
        # STATIC 32-byte word with the pair left-packed into the high 24 bytes,
        # (addr << 96) | (sel << 64) — verified empirically against solc
        # 0.8.35: `abi.encode(<fn value>)` emits exactly this word and solc's
        # calldata decoder round-trips it (and REVERTS on dirty low 64 bits,
        # which this packing leaves zero). The adjudicator's arg-domain
        # validation guarantees the 2-element shape and the u160/u32 ranges
        # before any encoding runs (fabrication fence); internal function
        # types never reach here (REJECTED_OOS upstream).
        if " external" not in ct:
            raise ValueError(f"internal function parameter {t!r} is not "
                             "ABI-encodable")
        if not isinstance(arg, list) or len(arg) != 2:
            raise ValueError(f"external function parameter {t!r} requires a "
                             f"2-element [address, selector] arg, got {arg!r}")
        addr, sel = (_arg_component_word(arg[0]), _arg_component_word(arg[1]))
        word = ((addr % (1 << 160)) << 96) | ((sel % (1 << 32)) << 64)
        return False, word.to_bytes(32, "big")
    members = obs._struct_member_types(ct, structs)
    if members is not None:
        if not isinstance(arg, list):
            raise ValueError(f"struct parameter {t!r} requires a JSON list arg "
                             f"(one element per member), got {arg!r}")
        if len(arg) != len(members):
            raise ValueError(f"struct {t!r} requires {len(members)} member "
                             f"values, got {len(arg)}")
        body = _encode_tuple_typed(arg, members, structs)
        return obs._is_dynamic_type(ct, structs), body
    if ct.startswith("struct "):
        raise ValueError(f"unresolvable struct parameter type {t!r}")
    if isinstance(arg, list):
        raise ValueError(f"scalar parameter {t!r} got a JSON list arg: {arg!r}")
    return _encode_arg(arg)


def _encode_tuple_typed(args: list, types: list[str],
                        structs: Optional[dict[str, list[str]]]) -> bytes:
    """ABI tuple (head+tail) encoding of ``args`` against ``types`` — the exact
    inverse of observable._decode_tuple: dynamic components hold an offset
    (relative to the region start) into the tail; static components (scalars,
    static fixed arrays, static structs) are inlined in the head."""
    encoded = [_encode_typed(a, t, structs) for a, t in zip(args, types)]
    head_size = sum(32 if is_dyn else len(enc) for is_dyn, enc in encoded)
    head = b""
    tail = b""
    for is_dyn, enc in encoded:
        if is_dyn:
            head += (head_size + len(tail)).to_bytes(32, "big")
            tail += enc
        else:
            head += enc
    return head + tail


def _encode_args_abi(args: list, types: Optional[list[str]] = None,
                     structs: Optional[dict[str, list[str]]] = None) -> bytes:
    """ABI-encode a positional arg list (head+tail), WITHOUT any selector prefix.

    Shared by the entry calldata (prepended with the 4-byte selector) and the
    constructor-argument tail appended to a contract's creationCode. With
    ``types`` (the parameter typeStrings from the compiled AST) the encoding is
    TYPE-DIRECTED, covering array/struct parameters; without it (legacy
    callers) only the scalar arg forms are encodable."""
    if types is not None:
        if len(args) != len(types):
            raise ValueError(f"arg count {len(args)} != parameter count "
                             f"{len(types)}")
        return _encode_tuple_typed(args, types, structs)
    encoded = [_encode_arg(a) for a in args]
    head = b""
    tail = b""
    head_size = 32 * len(encoded)
    for is_dyn, enc in encoded:
        if is_dyn:
            head += (head_size + len(tail)).to_bytes(32, "big")
            tail += enc
        else:
            head += enc
    return head + tail


def build_calldata(selector: str, args: list,
                   types: Optional[list[str]] = None,
                   structs: Optional[dict[str, list[str]]] = None) -> str:
    return selector + _encode_args_abi(args, types, structs).hex()


# ---------------------------------------------------------------------------
# Harness generation + run.
# ---------------------------------------------------------------------------

_VM_IFACE = """struct VmLog { bytes32[] topics; bytes data; address emitter; }

interface CVm {
    function roll(uint256) external;
    function warp(uint256) external;
    function chainId(uint256) external;
    function fee(uint256) external;
    function prevrandao(bytes32) external;
    function coinbase(address) external;
    function deal(address,uint256) external;
    function prank(address) external;
    function startPrank(address) external;
    function stopPrank() external;
    function recordLogs() external;
    function getRecordedLogs() external returns (VmLog[] memory);
    function record() external;
    function accesses(address) external returns (bytes32[] memory reads, bytes32[] memory writes);
    function load(address,bytes32) external view returns (bytes32);
    function store(address,bytes32,bytes32) external;
    function writeFile(string calldata, string calldata) external;
    function getNonce(address) external returns (uint64);
    function computeCreateAddress(address,uint256) external pure returns (address);
    function toString(bytes calldata) external pure returns (string memory);
    function toString(uint256) external pure returns (string memory);
    function toString(address) external pure returns (string memory);
}"""


def _harness_source(sig: EntrySig, calldata_hex: str, out_path: Path,
                    ov: cenv.EnvOverrides, rel_import: str,
                    slots: Optional[list[int]] = None,
                    ctor_args_hex: str = "",
                    inject_storage: Optional[list[tuple[int, int]]] = None) -> str:
    pin = [
        f"vm.roll({ov.number});",
        f"vm.warp({ov.timestamp});",
        f"vm.chainId({ov.chainid});",
        f"vm.fee({ov.basefee});",
        f"vm.prevrandao(bytes32(uint256({ov.prevrandao})));",
        f"vm.coinbase(address(uint160({ov.coinbase})));",
    ]
    # Use the last-wins-normalized deals so the EVM balance matches the solidity-lean
    # (first-wins list) balance for a repeated deal to the same address (env.py
    # effective_deals). vm.deal SETS a balance, so emitting only the last amount
    # per address is equivalent to replaying them all and strictly clearer.
    for addr, amt in ov.effective_deals():
        pin.append(f"vm.deal(address(uint160({addr})), {amt});")
    if ov.value:
        pin.append(f"vm.deal(address(this), {ov.value});")
    pin_block = "\n        ".join(pin)
    value_opt = f"{{value: {ov.value}}}" if ov.value else ""
    # Observed storage (§3.4 component 5), BROAD auto-detection (contest #8): we no
    # longer trust a submitter-declared slot list. `vm.record()` (armed before the
    # deploy, so constructor writes are captured too) lets `vm.accesses(target)`
    # report EVERY slot the contract wrote across deploy + entry call; we vm.load
    # each and emit `slot:value`. Duplicate slots and zero values are normalized
    # away by the Python comparator (observable._parse_storage_map), so no dedup is
    # needed here. This mirrors the solidity-lean side, which dumps its whole storage map.
    _ = slots  # retained for signature compatibility; superseded by vm.accesses
    # Deployment: ALWAYS a low-level CREATE from the contract's creationCode with
    # the ABI-encoded constructor args appended (the exact bytes solc would
    # append; empty for a no-arg constructor). This mirrors the solidity-lean
    # side, which runs `constructWithContext` with the same decoded args. A
    # low-level create (unlike `new C()`) does NOT abort the test when the
    # CONSTRUCTOR reverts: a constructor-revert is a first-class measurable
    # observable — the revert data (Error(string) / Panic / custom error /
    # empty) is captured via returndatacopy and dumped as `deployrevert|...`,
    # with self= the PREDICTED create address (computeCreateAddress over the
    # pranked deployer's nonce — identical to the actual address on success),
    # so address(this) inside the model's constructor still mirrors the EVM.
    sender_expr = f"address(uint160({ov.sender}))"
    deploy_block = (
        f'bytes memory _init = abi.encodePacked('
        f'type({sig.contract}).creationCode, hex"{ctor_args_hex}");\n'
        f'        address _pred = vm.computeCreateAddress({sender_expr}, '
        f'vm.getNonce({sender_expr}));\n'
        # Prank the DEPLOY (vm.prank applies to the next CALL or CREATE), so
        # the constructor's msg.sender is the canonical sender — the same value
        # solidity-lean threads into constructWithContext. Without this the
        # ctor would see the test-harness address and `owner = msg.sender`
        # would diverge. (Cheatcode calls above do not consume the prank.)
        f'        vm.prank({sender_expr});\n'
        f'        address _addr;\n'
        f'        assembly {{ _addr := create(0, add(_init, 0x20), mload(_init)) }}\n'
        f'        if (_addr == address(0)) {{\n'
        f'            bytes memory _crd;\n'
        f'            assembly {{\n'
        f'                _crd := mload(0x40)\n'
        f'                mstore(_crd, returndatasize())\n'
        f'                returndatacopy(add(_crd, 0x20), 0, returndatasize())\n'
        f'                mstore(0x40, add(add(_crd, 0x20), '
        f'and(add(returndatasize(), 0x3f), not(0x1f))))\n'
        f'            }}\n'
        f'            vm.writeFile("{out_path}", string(abi.encodePacked(\n'
        f'                "deployrevert|", vm.toString(_crd),\n'
        f'                "|self=", vm.toString(_pred),\n'
        f'                "|origin=", vm.toString(tx.origin),\n'
        f'                "|evt=|sto=")));\n'
        f'            return;\n'
        f'        }}\n'
        f'        {sig.contract} target = {sig.contract}(_addr);')
    # Raw storage injection (manifest `storage`): seed the entry contract's slots
    # AFTER the constructor runs, mirroring the solidity-lean side which seeds
    # deployState.storage post-construction. `vm.store` is a trusted cheatcode used
    # ONLY by this maintainer-controlled measurement harness (it is banned in
    # submissions); the submitter only declares the (slot, word) pairs. The Solidity
    # semantics is a total function over storage, so an injected state need not be
    # reachable by prior execution — both engines evaluate the same concrete state.
    inject = inject_storage or []
    inject_block = "\n        ".join(
        f'vm.store(address(target), bytes32(uint256({slot})), '
        f'bytes32(uint256({word})));'
        for slot, word in inject)
    # Injected slots must ALSO be emitted in the observed-storage section: vm.store
    # is a direct cheat poke that vm.accesses does NOT report, so an injected slot
    # the entry call never rewrites would appear on the solidity-lean side (whole-map
    # dump) but not here, fabricating a storage divergence. Emitting each injected
    # slot's post-call value (via vm.load) keeps the two sides symmetric; the Python
    # comparator drops zeros and dedups slots also written by the call.
    inject_sto_block = "\n            ".join(
        f'sto = abi.encodePacked(sto, ";", vm.toString(uint256({slot})), ":", '
        f'vm.toString(uint256(vm.load(address(target), bytes32(uint256({slot}))))));'
        for slot, _word in inject)
    return f"""// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {{{sig.contract}}} from "{rel_import}";

{_VM_IFACE}

contract ContestMeasure {{
    CVm constant vm = CVm({_CHEAT_EXPR});

    function test_ContestMeasure() public {{
        {pin_block}
        // Arm storage recording BEFORE the deploy so constructor SSTOREs count.
        vm.record();
        // Deploy (pranked; see deploy_block): a reverting constructor is
        // CAPTURED as the `deployrevert|...` observable, not a test abort.
        {deploy_block}
        // Raw storage injection (manifest `storage`), applied AFTER the constructor.
        {inject_block}
        vm.recordLogs();
        vm.prank(address(uint160({ov.sender})));
        (bool ok, bytes memory ret) = address(target).call{value_opt}(hex"{calldata_hex}");
        // Events (§3.4 component 4): rolled back on revert, so only on success.
        bytes memory evt = "";
        bytes memory sto = "";
        if (ok) {{
            VmLog[] memory logs = vm.getRecordedLogs();
            for (uint i = 0; i < logs.length; i++) {{
                bytes memory t = "t=[";
                for (uint j = 0; j < logs[i].topics.length; j++) {{
                    t = abi.encodePacked(t, j > 0 ? "," : "",
                        vm.toString(uint256(logs[i].topics[j])));
                }}
                t = abi.encodePacked(t, "];d=", vm.toString(logs[i].data));
                evt = abi.encodePacked(evt, i > 0 ? "~" : "", t);
            }}
            // Full post-call storage map: every written slot -> current value.
            (, bytes32[] memory ws) = vm.accesses(address(target));
            for (uint k = 0; k < ws.length; k++) {{
                sto = abi.encodePacked(sto, k > 0 ? ";" : "",
                    vm.toString(uint256(ws[k])), ":",
                    vm.toString(uint256(vm.load(address(target), ws[k]))));
            }}
            // Injected slots (see above): emit each post-call value so the observed
            // storage is symmetric with the solidity-lean whole-map dump.
            {inject_sto_block}
        }}
        string memory out = string(abi.encodePacked(
            ok ? "ok" : "revert", "|", vm.toString(ret),
            "|self=", vm.toString(address(target)),
            "|origin=", vm.toString(tx.origin),
            "|evt=", string(evt), "|sto=", string(sto)));
        vm.writeFile("{out_path}", out);
    }}
}}
"""


def measure_evm(sig: EntrySig, args: list, ov: cenv.EnvOverrides,
                work_dir: Path, forge: str, solc: str,
                repo: Path, timeout: int = 300,
                slots: Optional[list[int]] = None,
                constructor_args: Optional[list] = None,
                inject_storage: Optional[list[tuple[int, int]]] = None,
                ) -> tuple[Optional[Measurement], str]:
    """Generate + run the measurement harness; parse the raw entry-call result."""
    work_dir.mkdir(parents=True, exist_ok=True)
    proj = work_dir / "measure_proj"
    if proj.exists():
        shutil.rmtree(proj)
    (proj / "src").mkdir(parents=True)
    (proj / "test").mkdir(parents=True)

    # Copy ALL submitted src/*.sol into the harness project (review finding 6:
    # a submission may legitimately split a library/interface across files, and
    # copying only the entry file would fail to compile).
    for sol in sorted(sig.source_file.parent.glob("*.sol")):
        shutil.copy(sol, proj / "src" / sol.name)

    # The measurement output lives OUTSIDE the project tree (review finding 2):
    # the deployed submitter contract must not be able to write it. Only this
    # single file is granted to the (maintainer-controlled) measurement test, and
    # `ffi` stays disabled.
    out_path = (work_dir / "measure_out.txt").resolve()
    # TYPE-DIRECTED encoding (register >= 1.4.0): the entry parameter types and
    # the constructor's parameter types drive the head/tail layout, so array/
    # struct args ABI-encode exactly as solc's own encoder would (X-ARGVAL
    # retired). The struct table resolves struct params to member types.
    structs = struct_definitions(sig.source_file, solc)
    calldata = build_calldata(sig.selector, args, types=sig.param_types,
                              structs=structs)
    ctor_types = constructor_param_types(sig.source_file, sig.contract, solc)
    ctor_list = list(constructor_args or [])
    # Only encode type-directed when the arity matches (validated upstream);
    # a mismatch here would mean a caller bypassed validation — fall back to
    # the legacy scalar path, which raises on unencodable shapes.
    if len(ctor_types) == len(ctor_list):
        ctor_args_hex = _encode_args_abi(ctor_list, types=ctor_types,
                                         structs=structs).hex()
    else:
        ctor_args_hex = _encode_args_abi(ctor_list).hex()
    rel_import = f"../src/{sig.source_file.name}"
    (proj / "test" / "ContestMeasure.t.sol").write_text(
        _harness_source(sig, calldata, out_path, ov, rel_import, slots,
                        ctor_args_hex=ctor_args_hex,
                        inject_storage=inject_storage))
    (proj / "foundry.toml").write_text(
        "[profile.default]\nsrc = \"src\"\ntest = \"test\"\n"
        "evm_version = \"cancun\"\nffi = false\n"
        f"fs_permissions = [{{ access = \"write\", path = \"{out_path}\" }}]\n")

    args_cmd = [
        forge, "test",
        "--root", str(proj.resolve()),
        "--use", solc,
        "--no-auto-detect", "--offline", "--force",
        "--match-contract", "ContestMeasure",
        "--out", str((work_dir / "forge-out").resolve()),
        "--cache-path", str((work_dir / "forge-cache").resolve()),
        "-q",
    ]
    stdout_log = work_dir / "measure.stdout.log"
    stderr_log = work_dir / "measure.stderr.log"
    from . import harness_bridge as hb  # local import to avoid a cycle at import
    try:
        rc = hb._HARNESS.run_capture(args_cmd, repo, timeout, stdout_log, stderr_log)
    except Exception as exc:  # subprocess.TimeoutExpired etc.
        return None, f"measurement forge run failed: {exc}"
    if not out_path.exists():
        tail = _tail(stdout_log) + _tail(stderr_log)
        return None, f"measurement produced no output (forge rc={rc}); {tail}"
    raw = out_path.read_text().strip()
    m = _parse_measurement(raw)
    if m is None:
        return None, f"could not parse measurement output: {raw!r}"
    return m, "ok"


def _tail(path: Path, n: int = 600) -> str:
    try:
        return path.read_text(errors="replace")[-n:]
    except OSError:
        return ""


# ret_hex (group 2) MUST be even-length hex: it is later `bytes.fromhex`'d (in
# evm_observable's decoders and adjudicate.py's custom-error gate), which raises an
# UNCAUGHT ValueError on an odd-length string. `0x[0-9a-fA-F]*` admitted an odd count
# (e.g. `0xabc`), so a malformed measurement would crash the adjudicator instead of
# failing safe. Requiring pairs `(?:..){2}` makes a malformed ret_hex simply not
# match -> _parse_measurement returns None -> INVALID (fail-safe), never a crash.
_MEAS_RE = re.compile(
    r"^(ok|revert|deployrevert)\|(0x(?:[0-9a-fA-F]{2})*)"
    r"\|self=(0x[0-9a-fA-F]+)\|origin=(0x[0-9a-fA-F]+)"
    r"(?:\|evt=(.*)\|sto=(.*))?$")


def _parse_measurement(raw: str) -> Optional[Measurement]:
    match = _MEAS_RE.match(raw.strip())
    if not match:
        return None
    kind = match.group(1)
    ok = kind == "ok"
    deploy_reverted = kind == "deployrevert"
    ret_hex = match.group(2)
    self_addr = int(match.group(3), 16)
    origin = int(match.group(4), 16)
    events = match.group(5) or ""
    storage = match.group(6) or ""
    return Measurement(ok, ret_hex, self_addr, origin, raw,
                       events=events, storage=storage,
                       deploy_reverted=deploy_reverted)

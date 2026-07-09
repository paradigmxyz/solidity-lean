#!/usr/bin/env python3
"""Measure the EVM-side observable from an ACTUAL Forge run (review P0 #1).

The v1 adjudicator diffed Solidus against ``claim.declared_observable`` - an
entrant-controlled string (review O-1, CONTEST-BREAKING). This module instead
MEASURES the EVM observable: it generates a tiny Foundry harness that deploys the
entry contract, replays the whitelisted env cheatcodes (so the EVM env == the
canonical pinned env, contest/env.py), performs the ENTRY call by raw calldata,
and dumps the raw ``(ok, ret-bytes, self, origin)`` to a file. The adjudicator
decodes those bytes (observable.evm_observable) into the same normal form Solidus
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


@dataclass
class Measurement:
    ok: bool                 # entry call succeeded (True) vs reverted (False)
    ret_hex: str             # raw return (ok) or revert (not ok) bytes, 0x-hex
    self_addr: int           # deployed entry-contract address (mirror -> Solidus)
    origin: int
    raw: str                 # the raw dumped line, for evidence
    events: str = ""         # rendered events section (§3.4 component 4)
    storage: str = ""        # rendered observed-storage section (component 5)


# ---------------------------------------------------------------------------
# AST extraction of the entry function signature.
# ---------------------------------------------------------------------------

def entry_signature(source: Path, contract: str, function: str,
                    solc: str) -> Optional[EntrySig]:
    _name, ast = gate._IMPORTER.run_solc_ast(solc, source)
    for node in gate.iter_nodes(ast):
        if node.get("nodeType") != "ContractDefinition" or node.get("name") != contract:
            continue
        for item in node.get("nodes", []):
            if (item.get("nodeType") == "FunctionDefinition"
                    and item.get("name") == function):
                selector = item.get("functionSelector")
                if not selector:
                    return None
                params = [_param_type(p) for p in
                          item.get("parameters", {}).get("parameters", [])]
                returns = [_param_type(p) for p in
                           item.get("returnParameters", {}).get("parameters", [])]
                return EntrySig(selector, params, returns, source, contract)
    return None


def _param_type(p: dict[str, Any]) -> str:
    td = p.get("typeDescriptions") or {}
    return str(td.get("typeString") or "")


def error_definitions(source: Path, solc: str) -> dict[str, tuple[str, list[str]]]:
    """Map each user-defined error's 4-byte selector (8 lowercase hex, no 0x) to
    ``(name, [param_type, ...])`` from the compiled AST, so the EVM side can
    decode a custom-error revert into the ``custom:<Name>:...`` normal form.

    Uses solc's own ``errorSelector`` on each ``ErrorDefinition`` node (no keccak
    dependency); errors without a selector are skipped."""
    out: dict[str, tuple[str, list[str]]] = {}
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
        out[str(sel).lower()] = (str(name), types)
    return out


# ---------------------------------------------------------------------------
# Python-side ABI encoding of the entry args (from claim.json) into calldata.
# Supports the same v1 arg forms the Solidus renderer supports: word / int /
# bytes / bool. Static args go in the head; dynamic bytes get an offset+tail.
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


def _encode_args_abi(args: list) -> bytes:
    """ABI-encode a positional arg list (head+tail), WITHOUT any selector prefix.

    Shared by the entry calldata (prepended with the 4-byte selector) and the
    constructor-argument tail appended to a contract's creationCode."""
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


def build_calldata(selector: str, args: list) -> str:
    return selector + _encode_args_abi(args).hex()


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
    function writeFile(string calldata, string calldata) external;
    function toString(bytes calldata) external pure returns (string memory);
    function toString(uint256) external pure returns (string memory);
    function toString(address) external pure returns (string memory);
}"""


def _harness_source(sig: EntrySig, calldata_hex: str, out_path: Path,
                    ov: cenv.EnvOverrides, rel_import: str,
                    slots: Optional[list[int]] = None,
                    ctor_args_hex: str = "") -> str:
    pin = [
        f"vm.roll({ov.number});",
        f"vm.warp({ov.timestamp});",
        f"vm.chainId({ov.chainid});",
        f"vm.fee({ov.basefee});",
        f"vm.prevrandao(bytes32(uint256({ov.prevrandao})));",
        f"vm.coinbase(address(uint160({ov.coinbase})));",
    ]
    for addr, amt in ov.deals:
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
    # needed here. This mirrors the Solidus side, which dumps its whole storage map.
    _ = slots  # retained for signature compatibility; superseded by vm.accesses
    # Deployment: `new C()` for a no-arg constructor; otherwise deploy from the
    # contract's creationCode with the ABI-encoded constructor args appended (the
    # exact bytes solc would append), via a low-level CREATE. This mirrors the
    # Solidus side, which runs `constructWithContext` with the same decoded args.
    if ctor_args_hex:
        deploy_block = (
            f'bytes memory _init = abi.encodePacked('
            f'type({sig.contract}).creationCode, hex"{ctor_args_hex}");\n'
            f'        address _addr;\n'
            f'        assembly {{ _addr := create(0, add(_init, 0x20), mload(_init)) }}\n'
            f'        require(_addr != address(0), "constructor deploy reverted");\n'
            f'        {sig.contract} target = {sig.contract}(_addr);')
    else:
        deploy_block = f'{sig.contract} target = new {sig.contract}();'
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
        // Prank the DEPLOY too (vm.prank applies to the next CALL or CREATE), so
        // the constructor's msg.sender is the canonical sender — the same value
        // Solidus threads into constructWithContext. Without this the ctor would
        // see the test-harness address and `owner = msg.sender` would diverge.
        vm.prank(address(uint160({ov.sender})));
        {deploy_block}
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
                constructor_args: Optional[list] = None) -> tuple[Optional[Measurement], str]:
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
    calldata = build_calldata(sig.selector, args)
    ctor_args_hex = _encode_args_abi(constructor_args or []).hex()
    rel_import = f"../src/{sig.source_file.name}"
    (proj / "test" / "ContestMeasure.t.sol").write_text(
        _harness_source(sig, calldata, out_path, ov, rel_import, slots,
                        ctor_args_hex=ctor_args_hex))
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


_MEAS_RE = re.compile(
    r"^(ok|revert)\|(0x[0-9a-fA-F]*)\|self=(0x[0-9a-fA-F]+)\|origin=(0x[0-9a-fA-F]+)"
    r"(?:\|evt=(.*)\|sto=(.*))?$")


def _parse_measurement(raw: str) -> Optional[Measurement]:
    match = _MEAS_RE.match(raw.strip())
    if not match:
        return None
    ok = match.group(1) == "ok"
    ret_hex = match.group(2)
    self_addr = int(match.group(3), 16)
    origin = int(match.group(4), 16)
    events = match.group(5) or ""
    storage = match.group(6) or ""
    return Measurement(ok, ret_hex, self_addr, origin, raw,
                       events=events, storage=storage)

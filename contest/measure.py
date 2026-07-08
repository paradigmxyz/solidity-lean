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


def build_calldata(selector: str, args: list) -> str:
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
    return selector + (head + tail).hex()


# ---------------------------------------------------------------------------
# Harness generation + run.
# ---------------------------------------------------------------------------

_VM_IFACE = """interface CVm {
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
    function writeFile(string calldata, string calldata) external;
    function toString(bytes calldata) external pure returns (string memory);
    function toString(address) external pure returns (string memory);
}"""


def _harness_source(sig: EntrySig, calldata_hex: str, out_path: Path,
                    ov: cenv.EnvOverrides, rel_import: str) -> str:
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
    return f"""// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {{{sig.contract}}} from "{rel_import}";

{_VM_IFACE}

contract ContestMeasure {{
    CVm constant vm = CVm({_CHEAT_EXPR});

    function test_ContestMeasure() public {{
        {pin_block}
        {sig.contract} target = new {sig.contract}();
        vm.prank(address(uint160({ov.sender})));
        (bool ok, bytes memory ret) = address(target).call{value_opt}(hex"{calldata_hex}");
        string memory out = string(abi.encodePacked(
            ok ? "ok" : "revert", "|", vm.toString(ret),
            "|self=", vm.toString(address(target)),
            "|origin=", vm.toString(tx.origin)));
        vm.writeFile("{out_path}", out);
    }}
}}
"""


def measure_evm(sig: EntrySig, args: list, ov: cenv.EnvOverrides,
                work_dir: Path, forge: str, solc: str,
                repo: Path, timeout: int = 300) -> tuple[Optional[Measurement], str]:
    """Generate + run the measurement harness; parse the raw entry-call result."""
    work_dir.mkdir(parents=True, exist_ok=True)
    proj = work_dir / "measure_proj"
    if proj.exists():
        shutil.rmtree(proj)
    (proj / "src").mkdir(parents=True)
    (proj / "test").mkdir(parents=True)

    # Copy the entry source (single-contract v1) into the harness project.
    src_dst = proj / "src" / sig.source_file.name
    shutil.copy(sig.source_file, src_dst)

    out_path = (proj / "measure_out.txt").resolve()
    calldata = build_calldata(sig.selector, args)
    rel_import = f"../src/{sig.source_file.name}"
    (proj / "test" / "ContestMeasure.t.sol").write_text(
        _harness_source(sig, calldata, out_path, ov, rel_import))
    (proj / "foundry.toml").write_text(
        "[profile.default]\nsrc = \"src\"\ntest = \"test\"\n"
        "evm_version = \"cancun\"\n"
        f"fs_permissions = [{{ access = \"read-write\", path = \"{proj.resolve()}\" }}]\n")

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
    r"^(ok|revert)\|(0x[0-9a-fA-F]*)\|self=(0x[0-9a-fA-F]+)\|origin=(0x[0-9a-fA-F]+)$")


def _parse_measurement(raw: str) -> Optional[Measurement]:
    match = _MEAS_RE.match(raw.strip())
    if not match:
        return None
    ok = match.group(1) == "ok"
    ret_hex = match.group(2)
    self_addr = int(match.group(3), 16)
    origin = int(match.group(4), 16)
    return Measurement(ok, ret_hex, self_addr, origin, raw)

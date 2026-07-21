#!/usr/bin/env python3
"""Single-file submission format: one ``.sol`` with an embedded arena manifest.

A submission is a single Solidity file. It contains the contract(s) under test and
a JSON **manifest** in a header comment that tells the harness how to deploy and
call them:

    // SPDX-License-Identifier: MIT
    pragma solidity 0.8.35;

    /* ===ARENA-MANIFEST===
    {
      "deploy":  { "contract": "C", "args": [], "value": 0 },
      "entry":   { "function": "run", "args": [] },
      "env":     { "blockNumber": 1, "balances": { "0x..": 1000 } },
      "storage": { "0x0": "0x..ff" }
    }
    ===END-ARENA-MANIFEST=== */

    contract C { ... }

This module extracts + validates the manifest and ADAPTS it onto the shape the
(heavily hardened) directory-format adjudicator already consumes: it materializes
a ``src/Submission.sol`` + ``claim.json`` (no submitter test — the manifest IS the
harness's own measurement recipe), builds the ``EnvOverrides`` from ``env``, and
turns ``storage`` into the raw slot-injection list. All the deep validation (arg
domains, signature match, cheatcode/reject gate, X-RETABI, dedup) is inherited
unchanged from :mod:`adjudicate`; this front-end only does the single-file framing.

See ``SUBMISSION_FORMAT.md`` for the authored spec.
"""

from __future__ import annotations

import json
import re
import tempfile
from pathlib import Path
from typing import Any, Optional

from . import env as cenv


MANIFEST_BEGIN = "===ARENA-MANIFEST==="
MANIFEST_END = "===END-ARENA-MANIFEST==="

_UINT256 = 1 << 256
_UINT160 = 1 << 160
_MAX_INJECT_SLOTS = 64

# env field name (manifest) -> EnvOverrides attribute.
# Env fields a submitter may PIN. Each MUST be mirrorable into BOTH engines -
# the Lean context (env.py) AND the Foundry measurement (measure.py cheatcode).
# `gaslimit` is intentionally NOT here: Foundry has no cheatcode to set
# block.gaslimit, so pinning it would move only the Lean side and manufacture a
# false SOUNDNESS_GAP. The canonical block.gaslimit still applies on both sides
# by default (they agree); it just cannot be overridden.
_ENV_FIELDS: dict[str, str] = {
    "blockNumber": "number",
    "timestamp": "timestamp",
    "chainId": "chainid",
    "basefee": "basefee",
    "coinbase": "coinbase",
    "prevrandao": "prevrandao",
}

# Fields the Foundry EVM replay bounds to 64 bits (block.number / block.timestamp
# via vm.roll/vm.warp, chain id via vm.chainId which requires < 2^64); a >u64 pin
# passes uint256 validation but crashes the forge replay -> a dead-end failure.
# Cap them so an out-of-range pin is a clean REJECT_MALFORMED with a clear
# message instead. (release audit: chainId added — Foundry rejects >= 2^64.)
_ENV_U64_FIELDS = {"blockNumber", "timestamp", "chainId"}
_UINT64 = 1 << 64
# coinbase is an address (the harness emits `address(uint160(N))`); a >u160
# value would silently truncate on the EVM side while the Lean side kept the
# full magnitude — a fabricated env divergence. Bound it to the address domain.
_ENV_U160_FIELDS = {"coinbase"}

_IDENT_RE = re.compile(r"^[A-Za-z_$][A-Za-z0-9_$]*$")


# ---------------------------------------------------------------------------
# Extraction
# ---------------------------------------------------------------------------

def extract_manifest(text: str) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    """Pull the single manifest JSON object out of a ``.sol`` file's comment.

    Returns ``(manifest, None)`` on success or ``(None, error)``. Requires exactly
    one ``===ARENA-MANIFEST=== … ===END-ARENA-MANIFEST===`` block, whose body is a
    JSON object."""
    n_begin = text.count(MANIFEST_BEGIN)
    n_end = text.count(MANIFEST_END)
    if n_begin == 0:
        return None, (f"no manifest found: expected a {MANIFEST_BEGIN!r} … "
                      f"{MANIFEST_END!r} block in a comment")
    if n_begin > 1 or n_end > 1:
        return None, "more than one manifest block found; exactly one is required"
    if n_end == 0:
        return None, f"manifest opening marker has no matching {MANIFEST_END!r}"
    start = text.index(MANIFEST_BEGIN) + len(MANIFEST_BEGIN)
    end = text.index(MANIFEST_END)
    if end < start:
        return None, "manifest end marker appears before the begin marker"
    # The begin marker must sit inside an OPEN block comment: a `/*` before it
    # with no interleaved `*/`. Otherwise solc reads the "manifest" as code
    # while this extractor still honours it (mirror image of the check below).
    comment_open = text.rfind("/*", 0, start)
    if comment_open == -1 or "*/" in text[comment_open + 2:start - len(MANIFEST_BEGIN)]:
        return None, ("manifest begin marker is not inside an open /* comment; "
                      "the manifest block must be one uninterrupted block "
                      "comment")
    # Parser-differential guard: solc ends the enclosing /* ... */ comment at the
    # FIRST `*/`, but this extractor scans to the END marker by string index. A
    # `*/` inside the block (e.g. in a note) would make solc compile trailing
    # manifest text as CODE while the harness still reads it as manifest —
    # letting a submission show one program to solc and another to the pipeline.
    # The two readers must agree, so an early `*/` is a hard reject.
    if "*/" in text[start:end]:
        return None, ("manifest block contains '*/' before the end marker; solc "
                      "would close the comment there and compile the rest of the "
                      "block as code (parser differential) — remove '*/' from "
                      "the manifest body")
    body = text[start:end].strip()
    try:
        manifest = json.loads(body)
    except json.JSONDecodeError as exc:
        return None, f"manifest is not valid JSON: {exc}"
    if not isinstance(manifest, dict):
        return None, "manifest must be a JSON object"
    return manifest, None


# ---------------------------------------------------------------------------
# Validation (structural only — the adjudicator does the deep semantic checks)
# ---------------------------------------------------------------------------

def _as_int(v: object) -> Optional[int]:
    """Parse a manifest numeric/hex value to int, or None if not parseable.

    A JSON bool is rejected (it is not a numeric field here)."""
    if isinstance(v, bool):
        return None
    if isinstance(v, int):
        return v
    if isinstance(v, str):
        s = v.strip()
        try:
            return int(s, 16) if s.lower().startswith("0x") else int(s)
        except ValueError:
            return None
    return None


def validate_manifest(m: dict[str, Any]) -> Optional[str]:
    """Structural validation of a manifest; returns an error string or None."""
    # deploy
    deploy = m.get("deploy")
    if not isinstance(deploy, dict):
        return "manifest.deploy is required and must be an object"
    contract = deploy.get("contract")
    if not (isinstance(contract, str) and _IDENT_RE.match(contract)):
        return f"manifest.deploy.contract must be an identifier, got {contract!r}"
    if "args" in deploy and not isinstance(deploy["args"], list):
        return "manifest.deploy.args must be a list"
    if "value" in deploy and _as_int(deploy["value"]) is None:
        return f"manifest.deploy.value must be an integer, got {deploy['value']!r}"
    # entry
    entry = m.get("entry")
    if not isinstance(entry, dict):
        return "manifest.entry is required and must be an object"
    function = entry.get("function")
    if not (isinstance(function, str) and _IDENT_RE.match(function)):
        return f"manifest.entry.function must be an identifier, got {function!r}"
    if "args" in entry and not isinstance(entry["args"], list):
        return "manifest.entry.args must be a list"
    if "value" in entry and _as_int(entry["value"]) is None:
        return f"manifest.entry.value must be an integer, got {entry['value']!r}"
    if entry.get("caller") is not None:
        c = _as_int(entry["caller"])
        if c is None or not 0 <= c < _UINT160:
            return f"manifest.entry.caller must be an address, got {entry['caller']!r}"
    # env
    env = m.get("env")
    if env is not None:
        if not isinstance(env, dict):
            return "manifest.env must be an object"
        for k, v in env.items():
            if k == "balances":
                if not isinstance(v, dict):
                    return "manifest.env.balances must be an object of address->amount"
                for addr, amt in v.items():
                    a, n = _as_int(addr), _as_int(amt)
                    if a is None or not 0 <= a < _UINT160:
                        return f"manifest.env.balances key not an address: {addr!r}"
                    if n is None or not 0 <= n < _UINT256:
                        return f"manifest.env.balances[{addr}] out of range: {amt!r}"
                continue
            if k not in _ENV_FIELDS:
                return (f"manifest.env has unknown field {k!r}; allowed: "
                        f"{sorted(_ENV_FIELDS) + ['balances']}")
            iv = _as_int(v)
            if iv is None:
                return f"manifest.env.{k} must be an integer, got {v!r}"
            if k in _ENV_U64_FIELDS and not 0 <= iv < _UINT64:
                return (f"manifest.env.{k} must be in [0, 2**64) (the Foundry EVM "
                        f"replay bounds block.number/timestamp/chainId to 64 "
                        f"bits), got {v!r}")
            if k in _ENV_U160_FIELDS and not 0 <= iv < _UINT160:
                return (f"manifest.env.{k} must be an address in [0, 2**160), "
                        f"got {v!r}")
            # every env field must at least fit a uint256: an oversized value
            # would fail to compile into the measurement harness (a dead-end
            # failure) or truncate asymmetrically (a fabricated divergence).
            if not 0 <= iv < _UINT256:
                return f"manifest.env.{k} out of uint256 range: {v!r}"
    # storage (raw slot injection)
    storage = m.get("storage")
    if storage is not None:
        if not isinstance(storage, dict):
            return "manifest.storage must be an object of slot->word"
        if len(storage) > _MAX_INJECT_SLOTS:
            return f"manifest.storage has more than {_MAX_INJECT_SLOTS} slots"
        for slot, word in storage.items():
            s, w = _as_int(slot), _as_int(word)
            if s is None or not 0 <= s < _UINT256:
                return f"manifest.storage slot out of uint256 range: {slot!r}"
            if w is None or not 0 <= w < _UINT256:
                return f"manifest.storage[{slot}] word out of uint256 range: {word!r}"
    # optional scalars
    if "overAccept" in m and not isinstance(m["overAccept"], bool):
        return "manifest.overAccept must be a boolean"
    if "note" in m and not isinstance(m["note"], str):
        return "manifest.note must be a string"
    if "fuel" in m and _as_int(m["fuel"]) is None:
        return "manifest.fuel must be an integer"
    return None


# ---------------------------------------------------------------------------
# Adaptation onto the directory-format adjudicator
# ---------------------------------------------------------------------------

def claim_from_manifest(m: dict[str, Any]) -> dict[str, Any]:
    """Translate a validated manifest into the legacy ``claim.json`` dict."""
    deploy, entry = m["deploy"], m["entry"]
    over = bool(m.get("overAccept"))
    note = m.get("note") or ""
    claim: dict[str, Any] = {
        "_manifest": True,
        # lane is not used to decide the verdict (the harness measures it); a
        # sensible default keeps the loader's lane check happy. overAccept programs
        # are the soundness sub-case (solc rejects, solidity-lean runs).
        "lane": "S" if over else "C",
        "entry": {
            "contract": deploy["contract"],
            "function": entry["function"],
            "args": entry.get("args", []),
            "value": _as_int(entry.get("value", 0)) or 0,
            "constructor_args": deploy.get("args", []),
        },
        "feature": (m.get("feature") or (note[:60] if note else "")
                    or "unspecified-feature"),
        "fuel": _as_int(m.get("fuel", 64)) or 64,
    }
    if note:
        claim["expected_divergence"] = note
    if over:
        claim["_over_accept"] = True
        claim["mode"] = "OVER_ACCEPT"
        code = m.get("solcErrorCode")
        if code:
            claim["solc_error_code"] = code
    return claim


def env_from_manifest(m: dict[str, Any]) -> cenv.EnvOverrides:
    """Build the ``EnvOverrides`` (mirrored into both engines) from ``env`` +
    ``entry.value`` + ``entry.caller``."""
    ov = cenv.EnvOverrides()
    env = m.get("env") or {}
    for k, attr in _ENV_FIELDS.items():
        if k in env:
            setattr(ov, attr, _as_int(env[k]))
    for addr, amt in (env.get("balances") or {}).items():
        ov.deals.append((_as_int(addr), _as_int(amt)))
    entry = m["entry"]
    if "value" in entry:
        ov.value = _as_int(entry["value"]) or 0
    # entry.caller = vm.prank: sets msg.sender (for BOTH the deploy and the entry
    # call, as the single mirrored sender); tx.origin stays canonical.
    if entry.get("caller") is not None:
        ov.sender = _as_int(entry["caller"])
    return ov


def inject_storage_from_manifest(m: dict[str, Any]) -> list[tuple[int, int]]:
    """The raw (slot, word) pairs to seed into the entry contract's storage."""
    storage = m.get("storage") or {}
    return [(_as_int(slot), _as_int(word)) for slot, word in storage.items()]


def materialize(sol_text: str, claim: dict[str, Any], dest: Path) -> Path:
    """Write the single file out as the directory layout the adjudicator loads:
    ``src/Submission.sol`` + ``claim.json`` (no test/). The manifest comment is
    left in the source — solc ignores it — so the file is byte-identical to what
    the submitter wrote."""
    dest.mkdir(parents=True, exist_ok=True)
    (dest / "src").mkdir(exist_ok=True)
    (dest / "src" / "Submission.sol").write_text(sol_text, encoding="utf-8")
    (dest / "claim.json").write_text(json.dumps(claim, indent=2), encoding="utf-8")
    return dest


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def adjudicate_file(sol_path: Path, tools: Optional[Any] = None,
                    work_dir: Optional[Path] = None, timeout: int = 400,
                    at_version: Optional[str] = None) -> Any:
    """Adjudicate a single-file submission. Extract + validate the manifest, then
    delegate to the directory-format adjudicator in manifest mode."""
    from . import adjudicate as adj  # local import avoids an import cycle

    sol_path = Path(sol_path)
    if not sol_path.is_file():
        return adj.Report("REJECT_MALFORMED",
                          reason=f"submission file not found: {sol_path}")
    text = sol_path.read_text(encoding="utf-8", errors="replace")
    manifest, err = extract_manifest(text)
    if err is not None:
        return adj.Report("REJECT_MALFORMED", reason=err)
    assert manifest is not None
    verr = validate_manifest(manifest)
    if verr is not None:
        return adj.Report("REJECT_MALFORMED", reason=verr)

    work = work_dir or Path(tempfile.mkdtemp(prefix="contest-manifest."))
    sub_dir = materialize(text, claim_from_manifest(manifest), work / "submission")
    env_ov = env_from_manifest(manifest)
    inject = inject_storage_from_manifest(manifest)
    return adj.adjudicate(sub_dir, tools=tools, work_dir=work / "adj",
                          timeout=timeout, at_version=at_version,
                          env_override=env_ov, inject_storage=inject)


def _main(argv: Optional[list[str]] = None) -> int:
    import argparse
    from . import harness_bridge as hb

    p = argparse.ArgumentParser(
        description="Adjudicate a single-file (.sol + manifest) submission")
    p.add_argument("submission", type=Path, help="path to the single .sol file")
    p.add_argument("--solc", default=hb.DEFAULT_SOLC)
    p.add_argument("--forge", default=hb.DEFAULT_FORGE)
    p.add_argument("--lake", default=hb.DEFAULT_LAKE)
    p.add_argument("--timeout", type=int, default=400)
    p.add_argument("--work-dir", type=Path, default=None)
    p.add_argument("--json", action="store_true", help="emit JSON only")
    args = p.parse_args(argv)

    tools = hb.ToolPaths(solc=args.solc, forge=args.forge, lake=args.lake)
    report = adjudicate_file(args.submission, tools=tools,
                             work_dir=args.work_dir, timeout=args.timeout)
    print(json.dumps(report.to_dict(), indent=2))
    if not args.json:
        import sys
        print(f"\n=== VERDICT: {report.verdict}"
              + (f" (lane {report.lane})" if report.lane else "")
              + f" | qualifies={report.qualifies} ===", file=sys.stderr)
    return 0 if report.qualifies or report.verdict == "NO_DIVERGENCE" else 1


if __name__ == "__main__":
    raise SystemExit(_main())

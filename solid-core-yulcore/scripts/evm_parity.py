#!/usr/bin/env python3
"""Forge/Lean EVM parity harness.

Forge executes bytecode on Foundry's EVM and passes the observed result to this
checker through `vm.ffi`. The checker runs the same single-contract case through
the Lean executable and exits non-zero on any mismatch.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def normalize_hex(value: str, *, word: bool = False) -> str:
    raw = value.strip().lower()
    if raw.startswith("0x"):
        raw = raw[2:]
    if raw and len(raw) % 2:
        raw = "0" + raw
    if word:
        raw = raw.rjust(64, "0")[-64:]
    return "0x" + raw


def normalize_word(value: str) -> str:
    raw = value.strip().lower()
    if raw.startswith("0x"):
        return normalize_hex(raw, word=True)
    return "0x" + f"{int(raw):064x}"[-64:]


def normalize_log(value: str) -> str:
    address, topics, data = value.split("|", 2)
    normalized_topics = ",".join(
        normalize_hex(topic, word=True) for topic in topics.split(",") if topic
    )
    return "|".join(
        [normalize_hex(address, word=True), normalized_topics, normalize_hex(data)]
    )


def parse_lean_output(stdout: str) -> dict[str, object]:
    result: dict[str, object] = {
        "storage": {},
        "account_storage": {},
        "account_balance": {},
        "account_nonce": {},
        "account_code": {},
        "logs": [],
    }
    for line in stdout.splitlines():
        parts = line.strip().split()
        if not parts:
            continue
        if parts[0] == "storage" and len(parts) == 3:
            result["storage"][normalize_hex(parts[1], word=True)] = normalize_hex(
                parts[2], word=True
            )
        elif parts[0] == "account_storage" and len(parts) == 4:
            address = normalize_hex(parts[1], word=True)
            key = normalize_hex(parts[2], word=True)
            result["account_storage"][f"{address}:{key}"] = normalize_hex(
                parts[3], word=True
            )
        elif parts[0] == "account_balance" and len(parts) == 3:
            result["account_balance"][normalize_hex(parts[1], word=True)] = (
                normalize_hex(parts[2], word=True)
            )
        elif parts[0] == "account_nonce" and len(parts) == 3:
            result["account_nonce"][normalize_hex(parts[1], word=True)] = normalize_hex(
                parts[2], word=True
            )
        elif parts[0] == "account_code" and len(parts) == 3:
            result["account_code"][normalize_hex(parts[1], word=True)] = normalize_hex(
                parts[2]
            )
        elif parts[0] == "log" and len(parts) == 4:
            result["logs"].append(
                "|".join(
                    [
                        normalize_hex(parts[1], word=True),
                        parts[2].lower(),
                        normalize_hex(parts[3]),
                    ]
                )
            )
        elif len(parts) >= 2:
            result[parts[0]] = " ".join(parts[1:])
    return result


def run_lean(args: argparse.Namespace) -> dict[str, object]:
    exe = os.environ.get("EVM_PARITY_LEAN_EXE")
    built_exe = ROOT / ".lake" / "build" / "bin" / "evm_parity"
    if exe:
        cmd = [exe]
    elif built_exe.exists():
        cmd = [str(built_exe)]
    else:
        lake = Path.home() / ".elan" / "bin" / "lake"
        cmd = [str(lake), "exe", "evm_parity", "--"]
    cmd += [
        "--code",
        args.code,
        "--calldata",
        args.calldata,
        "--gas",
        str(args.gas),
        "--fuel",
        str(args.fuel),
        "--call-depth",
        str(args.call_depth),
        "--address",
        args.address,
        "--caller",
        args.caller,
        "--origin",
        args.origin,
        "--coinbase",
        args.coinbase,
        "--timestamp",
        str(args.timestamp),
        "--number",
        str(args.number),
        "--gaslimit",
        str(args.block_gas_limit),
        "--basefee",
        str(args.basefee),
        "--chainid",
        str(args.chainid),
        "--callvalue",
        args.callvalue,
        "--balance",
        args.balance,
        "--nonce",
        args.nonce,
    ]
    for item in args.storage:
        cmd += ["--storage", item]
    for item in args.original_storage:
        cmd += ["--original-storage", item]
    for item in args.account:
        cmd += ["--account", item]
    for item in args.account_balance:
        cmd += ["--account-balance", item]
    for item in args.account_nonce:
        cmd += ["--account-nonce", item]
    for item in args.account_storage:
        cmd += ["--account-storage", item]
    for item in args.account_original_storage:
        cmd += ["--account-original-storage", item]
    for item in args.keccak:
        cmd += ["--keccak", item]
    for item in args.warm_address:
        cmd += ["--warm-address", item]
    for item in args.warm_storage:
        cmd += ["--warm-storage", item]

    proc = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return parse_lean_output(proc.stdout)


def fail(case: str, mismatches: list[str], lean: dict[str, object]) -> None:
    print(f"EVM parity mismatch in {case}", file=sys.stderr)
    for mismatch in mismatches:
        print(f"  - {mismatch}", file=sys.stderr)
    print("Lean result:", lean, file=sys.stderr)
    raise SystemExit(1)


def check(args: argparse.Namespace) -> None:
    lean = run_lean(args)
    mismatches: list[str] = []

    expected_success = "1" if args.success else "0"
    if lean.get("success") != expected_success:
        mismatches.append(
            f"success: forge={expected_success} lean={lean.get('success')}"
        )

    expected_output = normalize_hex(args.output)
    if lean.get("output") != expected_output:
        mismatches.append(f"output: forge={expected_output} lean={lean.get('output')}")

    if str(lean.get("gas_used")) != str(args.gas_used):
        mismatches.append(
            f"gas_used: forge={args.gas_used} lean={lean.get('gas_used')}"
        )

    if str(lean.get("gas_remaining")) != str(args.gas_remaining):
        mismatches.append(
            "gas_remaining: "
            f"forge={args.gas_remaining} lean={lean.get('gas_remaining')}"
        )

    if str(lean.get("refund")) != str(args.gas_refunded):
        mismatches.append(
            f"refund: forge={args.gas_refunded} lean={lean.get('refund')}"
        )

    if args.expect_balance is not None:
        expected_balance = normalize_word(args.expect_balance)
        if lean.get("balance") != expected_balance:
            mismatches.append(
                f"balance: forge={expected_balance} lean={lean.get('balance')}"
            )

    if args.expect_nonce is not None:
        expected_nonce = normalize_word(args.expect_nonce)
        if lean.get("nonce") != expected_nonce:
            mismatches.append(f"nonce: forge={expected_nonce} lean={lean.get('nonce')}")

    lean_storage = lean.get("storage", {})
    assert isinstance(lean_storage, dict)
    for assignment in args.expect_storage:
        key, value = assignment.split("=", 1)
        key = normalize_hex(key, word=True)
        expected = normalize_hex(value, word=True)
        actual = lean_storage.get(key, "0x" + "0" * 64)
        if actual != expected:
            mismatches.append(f"storage[{key}]: forge={expected} lean={actual}")

    lean_account_storage = lean.get("account_storage", {})
    assert isinstance(lean_account_storage, dict)
    for assignment in args.expect_account_storage:
        address_and_key, value = assignment.split("=", 1)
        address, key = address_and_key.split(":", 1)
        address = normalize_hex(address, word=True)
        key = normalize_hex(key, word=True)
        expected = normalize_hex(value, word=True)
        actual = lean_account_storage.get(f"{address}:{key}", "0x" + "0" * 64)
        if actual != expected:
            mismatches.append(
                f"account_storage[{address}:{key}]: forge={expected} lean={actual}"
            )

    lean_account_balance = lean.get("account_balance", {})
    assert isinstance(lean_account_balance, dict)
    for assignment in args.expect_account_balance:
        address, value = assignment.split("=", 1)
        address = normalize_hex(address, word=True)
        expected = normalize_word(value)
        actual = lean_account_balance.get(address, "0x" + "0" * 64)
        if actual != expected:
            mismatches.append(
                f"account_balance[{address}]: forge={expected} lean={actual}"
            )

    lean_account_nonce = lean.get("account_nonce", {})
    assert isinstance(lean_account_nonce, dict)
    for assignment in args.expect_account_nonce:
        address, value = assignment.split("=", 1)
        address = normalize_hex(address, word=True)
        expected = normalize_word(value)
        actual = lean_account_nonce.get(address, "0x" + "0" * 64)
        if actual != expected:
            mismatches.append(
                f"account_nonce[{address}]: forge={expected} lean={actual}"
            )

    expected_logs = [normalize_log(log) for log in args.expect_log]
    lean_logs = lean.get("logs", [])
    assert isinstance(lean_logs, list)
    if lean_logs != expected_logs:
        mismatches.append(f"logs: forge={expected_logs} lean={lean_logs}")

    if mismatches:
        fail(args.case, mismatches, lean)

    print(f"ok {args.case}")


def forge(args: argparse.Namespace) -> None:
    cmd = [
        "forge",
        "test",
        "--root",
        str(ROOT / "forge-parity"),
        "--ffi",
        "--evm-version",
        "osaka",
        "--enable-tx-gas-limit",
        "--gas-limit",
        "16777216",
    ]
    if args.match_test:
        cmd += ["--match-test", args.match_test]
    raise SystemExit(subprocess.call(cmd, cwd=ROOT))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    check_p = sub.add_parser("check")
    check_p.add_argument("--case", required=True)
    check_p.add_argument("--code", required=True)
    check_p.add_argument("--calldata", default="0x")
    check_p.add_argument("--gas", type=int, required=True)
    check_p.add_argument("--fuel", type=int, default=200000)
    check_p.add_argument("--call-depth", type=int, default=16)
    check_p.add_argument("--success", type=int, choices=[0, 1], required=True)
    check_p.add_argument("--output", required=True)
    check_p.add_argument("--gas-used", type=int, required=True)
    check_p.add_argument("--gas-remaining", type=int, required=True)
    check_p.add_argument("--gas-refunded", type=int, required=True)
    check_p.add_argument("--address", default="0x1000000000000000000000000000000000000001")
    check_p.add_argument("--caller", default="0x1000000000000000000000000000000000000002")
    check_p.add_argument("--origin", default="0x1000000000000000000000000000000000000002")
    check_p.add_argument("--coinbase", default="0x0000000000000000000000000000000000000000")
    check_p.add_argument("--timestamp", type=int, default=1764798551)
    check_p.add_argument("--number", type=int, default=0)
    check_p.add_argument("--block-gas-limit", type=int, default=60000000)
    check_p.add_argument("--basefee", type=int, default=0)
    check_p.add_argument("--chainid", type=int, default=1)
    check_p.add_argument("--callvalue", default="0")
    check_p.add_argument("--balance", default="0")
    check_p.add_argument("--nonce", default="0")
    check_p.add_argument("--expect-balance")
    check_p.add_argument("--expect-nonce")
    check_p.add_argument("--storage", action="append", default=[])
    check_p.add_argument("--original-storage", action="append", default=[])
    check_p.add_argument("--expect-storage", action="append", default=[])
    check_p.add_argument("--account", action="append", default=[])
    check_p.add_argument("--account-balance", action="append", default=[])
    check_p.add_argument("--account-nonce", action="append", default=[])
    check_p.add_argument("--account-storage", action="append", default=[])
    check_p.add_argument("--account-original-storage", action="append", default=[])
    check_p.add_argument("--expect-account-storage", action="append", default=[])
    check_p.add_argument("--expect-account-balance", action="append", default=[])
    check_p.add_argument("--expect-account-nonce", action="append", default=[])
    check_p.add_argument("--expect-log", action="append", default=[])
    check_p.add_argument("--keccak", action="append", default=[])
    check_p.add_argument("--warm-address", action="append", default=[])
    check_p.add_argument("--warm-storage", action="append", default=[])
    check_p.set_defaults(func=check)

    forge_p = sub.add_parser("forge")
    forge_p.add_argument("--match-test")
    forge_p.set_defaults(func=forge)

    return parser


def main() -> None:
    args = build_parser().parse_args()
    args.func(args)


if __name__ == "__main__":
    main()

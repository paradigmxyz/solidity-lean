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


ROOT = Path(__file__).resolve().parents[2]
FORGE_PARITY_ROOT = ROOT / "tests" / "evm" / "forge-parity"


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
        "transient_storage": {},
        "account_storage": {},
        "account_transient_storage": {},
        "account_balance": {},
        "account_nonce": {},
        "account_code": {},
        "account_codesize": {},
        "account_codehash": {},
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
        elif parts[0] == "transient_storage" and len(parts) == 3:
            result["transient_storage"][normalize_hex(parts[1], word=True)] = (
                normalize_hex(parts[2], word=True)
            )
        elif parts[0] == "account_storage" and len(parts) == 4:
            address = normalize_hex(parts[1], word=True)
            key = normalize_hex(parts[2], word=True)
            result["account_storage"][f"{address}:{key}"] = normalize_hex(
                parts[3], word=True
            )
        elif parts[0] == "account_transient_storage" and len(parts) == 4:
            address = normalize_hex(parts[1], word=True)
            key = normalize_hex(parts[2], word=True)
            result["account_transient_storage"][f"{address}:{key}"] = normalize_hex(
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
        elif parts[0] == "account_codesize" and len(parts) == 3:
            result["account_codesize"][normalize_hex(parts[1], word=True)] = parts[2]
        elif parts[0] == "account_codehash" and len(parts) == 3:
            result["account_codehash"][normalize_hex(parts[1], word=True)] = (
                normalize_hex(parts[2], word=True)
            )
        elif parts[0] == "log" and len(parts) in (3, 4):
            topics = "" if len(parts) == 3 else parts[2].lower()
            data = parts[2] if len(parts) == 3 else parts[3]
            result["logs"].append(
                "|".join(
                    [
                        normalize_hex(parts[1], word=True),
                        topics,
                        normalize_hex(data),
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
        "--gasprice",
        args.gasprice,
        "--coinbase",
        args.coinbase,
        "--timestamp",
        str(args.timestamp),
        "--number",
        str(args.number),
        "--prevrandao",
        args.prevrandao,
        "--gaslimit",
        str(args.block_gas_limit),
        "--basefee",
        str(args.basefee),
        "--blobbasefee",
        str(args.blobbasefee),
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
    for item in args.blockhash:
        cmd += ["--blockhash", item]
    for item in args.blobhash:
        cmd += ["--blobhash", item]
    for item in args.keccak:
        cmd += ["--keccak", item]
    for item in args.sha256:
        cmd += ["--sha256", item]
    for item in args.ripemd160:
        cmd += ["--ripemd160", item]
    for item in args.modexp:
        cmd += ["--modexp", item]
    for item in args.blake2f:
        cmd += ["--blake2f", item]
    for item in args.ecadd:
        cmd += ["--ecadd", item]
    for item in args.ecmul:
        cmd += ["--ecmul", item]
    for item in args.ecpairing:
        cmd += ["--ecpairing", item]
    for item in args.ecadd_fail:
        cmd += ["--ecadd-fail", item]
    for item in args.ecmul_fail:
        cmd += ["--ecmul-fail", item]
    for item in args.ecpairing_fail:
        cmd += ["--ecpairing-fail", item]
    for item in args.point_evaluation:
        cmd += ["--point-evaluation", item]
    for item in args.point_evaluation_fail:
        cmd += ["--point-evaluation-fail", item]
    for item in args.p256_verify:
        cmd += ["--p256-verify", item]
    for item in args.p256_verify_fail:
        cmd += ["--p256-verify-fail", item]
    for item in args.bls_g1add:
        cmd += ["--bls-g1add", item]
    for item in args.bls_g1msm:
        cmd += ["--bls-g1msm", item]
    for item in args.bls_g2add:
        cmd += ["--bls-g2add", item]
    for item in args.bls_g2msm:
        cmd += ["--bls-g2msm", item]
    for item in args.bls_pairing:
        cmd += ["--bls-pairing", item]
    for item in args.bls_map_fp_to_g1:
        cmd += ["--bls-map-fp-to-g1", item]
    for item in args.bls_map_fp2_to_g2:
        cmd += ["--bls-map-fp2-to-g2", item]
    for item in args.bls_g1add_fail:
        cmd += ["--bls-g1add-fail", item]
    for item in args.bls_g1msm_fail:
        cmd += ["--bls-g1msm-fail", item]
    for item in args.bls_g2add_fail:
        cmd += ["--bls-g2add-fail", item]
    for item in args.bls_g2msm_fail:
        cmd += ["--bls-g2msm-fail", item]
    for item in args.bls_pairing_fail:
        cmd += ["--bls-pairing-fail", item]
    for item in args.bls_map_fp_to_g1_fail:
        cmd += ["--bls-map-fp-to-g1-fail", item]
    for item in args.bls_map_fp2_to_g2_fail:
        cmd += ["--bls-map-fp2-to-g2-fail", item]
    for item in args.cheat_addr:
        cmd += ["--cheat-addr", item]
    for item in args.cheat_sign:
        cmd += ["--cheat-sign", item]
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

    if not args.skip_gas:
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

    lean_transient_storage = lean.get("transient_storage", {})
    assert isinstance(lean_transient_storage, dict)
    for assignment in args.expect_transient_storage:
        key, value = assignment.split("=", 1)
        key = normalize_hex(key, word=True)
        expected = normalize_hex(value, word=True)
        actual = lean_transient_storage.get(key, "0x" + "0" * 64)
        if actual != expected:
            mismatches.append(
                f"transient_storage[{key}]: forge={expected} lean={actual}"
            )

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

    lean_account_transient_storage = lean.get("account_transient_storage", {})
    assert isinstance(lean_account_transient_storage, dict)
    for assignment in args.expect_account_transient_storage:
        address_and_key, value = assignment.split("=", 1)
        address, key = address_and_key.split(":", 1)
        address = normalize_hex(address, word=True)
        key = normalize_hex(key, word=True)
        expected = normalize_hex(value, word=True)
        actual = lean_account_transient_storage.get(
            f"{address}:{key}", "0x" + "0" * 64
        )
        if actual != expected:
            mismatches.append(
                "account_transient_storage"
                f"[{address}:{key}]: forge={expected} lean={actual}"
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

    lean_account_code = lean.get("account_code", {})
    assert isinstance(lean_account_code, dict)
    for assignment in args.expect_account_code:
        address, value = assignment.split("=", 1)
        address = normalize_hex(address, word=True)
        expected = normalize_hex(value)
        actual = lean_account_code.get(address, "0x")
        if actual != expected:
            mismatches.append(
                f"account_code[{address}]: forge={expected} lean={actual}"
            )

    lean_account_codesize = lean.get("account_codesize", {})
    assert isinstance(lean_account_codesize, dict)
    for assignment in args.expect_account_codesize:
        address, value = assignment.split("=", 1)
        address = normalize_hex(address, word=True)
        expected = str(int(value, 0))
        actual = lean_account_codesize.get(address, "0")
        if actual != expected:
            mismatches.append(
                f"account_codesize[{address}]: forge={expected} lean={actual}"
            )

    lean_account_codehash = lean.get("account_codehash", {})
    assert isinstance(lean_account_codehash, dict)
    for assignment in args.expect_account_codehash:
        address, value = assignment.split("=", 1)
        address = normalize_hex(address, word=True)
        expected = normalize_hex(value, word=True)
        actual = lean_account_codehash.get(address, "0x" + "0" * 64)
        if actual != expected:
            mismatches.append(
                f"account_codehash[{address}]: forge={expected} lean={actual}"
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
        str(FORGE_PARITY_ROOT),
        "--ffi",
        "--evm-version",
        "osaka",
        "--gas-limit",
        "33554432",
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
    check_p.add_argument("--skip-gas", action="store_true")
    check_p.add_argument("--gas-refunded", type=int, required=True)
    check_p.add_argument("--address", default="0x1000000000000000000000000000000000000001")
    check_p.add_argument("--caller", default="0x1000000000000000000000000000000000000002")
    check_p.add_argument("--origin", default="0x1000000000000000000000000000000000000002")
    check_p.add_argument("--gasprice", default="0")
    check_p.add_argument("--coinbase", default="0x0000000000000000000000000000000000000000")
    check_p.add_argument("--timestamp", type=int, default=1764798551)
    check_p.add_argument("--number", type=int, default=0)
    check_p.add_argument("--prevrandao", default="0")
    check_p.add_argument("--block-gas-limit", type=int, default=60000000)
    check_p.add_argument("--basefee", type=int, default=0)
    check_p.add_argument("--blobbasefee", type=int, default=0)
    check_p.add_argument("--chainid", type=int, default=1)
    check_p.add_argument("--blockhash", action="append", default=[])
    check_p.add_argument("--blobhash", action="append", default=[])
    check_p.add_argument("--callvalue", default="0")
    check_p.add_argument("--balance", default="0")
    check_p.add_argument("--nonce", default="0")
    check_p.add_argument("--expect-balance")
    check_p.add_argument("--expect-nonce")
    check_p.add_argument("--storage", action="append", default=[])
    check_p.add_argument("--original-storage", action="append", default=[])
    check_p.add_argument("--expect-storage", action="append", default=[])
    check_p.add_argument("--expect-transient-storage", action="append", default=[])
    check_p.add_argument("--account", action="append", default=[])
    check_p.add_argument("--account-balance", action="append", default=[])
    check_p.add_argument("--account-nonce", action="append", default=[])
    check_p.add_argument("--account-storage", action="append", default=[])
    check_p.add_argument("--account-original-storage", action="append", default=[])
    check_p.add_argument("--expect-account-storage", action="append", default=[])
    check_p.add_argument(
        "--expect-account-transient-storage", action="append", default=[]
    )
    check_p.add_argument("--expect-account-balance", action="append", default=[])
    check_p.add_argument("--expect-account-nonce", action="append", default=[])
    check_p.add_argument("--expect-account-code", action="append", default=[])
    check_p.add_argument("--expect-account-codesize", action="append", default=[])
    check_p.add_argument("--expect-account-codehash", action="append", default=[])
    check_p.add_argument("--expect-log", action="append", default=[])
    check_p.add_argument("--keccak", action="append", default=[])
    check_p.add_argument("--sha256", action="append", default=[])
    check_p.add_argument("--ripemd160", action="append", default=[])
    check_p.add_argument("--modexp", action="append", default=[])
    check_p.add_argument("--blake2f", action="append", default=[])
    check_p.add_argument("--ecadd", action="append", default=[])
    check_p.add_argument("--ecmul", action="append", default=[])
    check_p.add_argument("--ecpairing", action="append", default=[])
    check_p.add_argument("--ecadd-fail", action="append", default=[])
    check_p.add_argument("--ecmul-fail", action="append", default=[])
    check_p.add_argument("--ecpairing-fail", action="append", default=[])
    check_p.add_argument("--point-evaluation", action="append", default=[])
    check_p.add_argument("--point-evaluation-fail", action="append", default=[])
    check_p.add_argument("--p256-verify", action="append", default=[])
    check_p.add_argument("--p256-verify-fail", action="append", default=[])
    check_p.add_argument("--bls-g1add", action="append", default=[])
    check_p.add_argument("--bls-g1msm", action="append", default=[])
    check_p.add_argument("--bls-g2add", action="append", default=[])
    check_p.add_argument("--bls-g2msm", action="append", default=[])
    check_p.add_argument("--bls-pairing", action="append", default=[])
    check_p.add_argument("--bls-map-fp-to-g1", action="append", default=[])
    check_p.add_argument("--bls-map-fp2-to-g2", action="append", default=[])
    check_p.add_argument("--bls-g1add-fail", action="append", default=[])
    check_p.add_argument("--bls-g1msm-fail", action="append", default=[])
    check_p.add_argument("--bls-g2add-fail", action="append", default=[])
    check_p.add_argument("--bls-g2msm-fail", action="append", default=[])
    check_p.add_argument("--bls-pairing-fail", action="append", default=[])
    check_p.add_argument("--bls-map-fp-to-g1-fail", action="append", default=[])
    check_p.add_argument("--bls-map-fp2-to-g2-fail", action="append", default=[])
    check_p.add_argument("--cheat-addr", action="append", default=[])
    check_p.add_argument("--cheat-sign", action="append", default=[])
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

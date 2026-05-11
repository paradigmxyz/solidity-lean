#!/usr/bin/env python3
"""Replay simple Foundry artifact tests through the Lean EVM.

This is the first stateful runner slice: deploy one compiled test contract by
runtime bytecode, optionally call `setUp()`, then call no-argument `test*` or
`invariant*` functions while carrying the Lean account world between top-level
calls. It intentionally reports unsupported cases instead of guessing.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = ROOT / "tests" / "evm" / "forge-parity" / "foundry-suites.toml"
TARGET = "0x1000000000000000000000000000000000000001"
CALLER = "0x1000000000000000000000000000000000000002"
ORIGIN = CALLER
HEVM_ADDRESS = "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D"
DEFAULT_GAS = 60_000_000
DEFAULT_FUEL = 500_000
DEFAULT_INITIAL_BALANCE = 1 << 96
DEFAULT_INITIAL_NONCE = 1
MISSING_HASH_RE = re.compile(r"StepError\.missingHash\s+(\[[^\]]*\])", re.M)
MISSING_CHEAT_ADDR_RE = re.compile(r"missingCheatcodeAddress\s+([0-9]+)", re.M)
MISSING_CHEAT_SIGN_RE = re.compile(
    r"missingCheatcodeSignature\s+([0-9]+)\s+([0-9]+)", re.M
)
CHEATCODE_RE = re.compile(r"\b(?:vm|hevm)\.[A-Za-z_][A-Za-z0-9_]*\s*\(")


class UnsupportedReplay(Exception):
    pass


@dataclass
class AccountState:
    code: str = "0x"
    balance: str = "0"
    nonce: str = "0"
    storage: dict[str, str] = field(default_factory=dict)
    destroyed: bool = False


@dataclass
class World:
    root: str
    accounts: dict[str, AccountState]
    keccak: dict[str, str] = field(default_factory=dict)
    cheat_addrs: dict[str, str] = field(default_factory=dict)
    cheat_signs: dict[tuple[str, str], tuple[str, str, str]] = field(default_factory=dict)


@dataclass(frozen=True)
class ForgeExpectation:
    status: str
    gas: int | None

    @property
    def ok(self) -> bool:
        return self.status == "Success"


def normalize_hex(value: str, *, word: bool = False) -> str:
    raw = value.strip().lower()
    if raw.startswith("0x"):
        raw = raw[2:]
    if raw and len(raw) % 2:
        raw = "0" + raw
    if word:
        raw = raw.rjust(64, "0")[-64:]
    return "0x" + raw


def clone_account(account: AccountState) -> AccountState:
    return AccountState(
        code=account.code,
        balance=account.balance,
        nonce=account.nonce,
        storage=dict(account.storage),
        destroyed=account.destroyed,
    )


def clone_world(world: World) -> World:
    return World(
        world.root,
        {address: clone_account(account) for address, account in world.accounts.items()},
        dict(world.keccak),
        dict(world.cheat_addrs),
        dict(world.cheat_signs),
    )


def normalize_word(value: str) -> str:
    raw = value.strip().lower()
    if raw.startswith("0x"):
        return normalize_hex(raw, word=True)
    return "0x" + f"{int(raw):064x}"[-64:]


def word_to_short_hex(value: str) -> str:
    return hex(int(normalize_word(value), 16))


def cast_keccak(data_hex: str) -> str:
    proc = subprocess.run(
        ["cast", "keccak", data_hex],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return normalize_hex(proc.stdout.strip(), word=True)


def cast_wallet_address(private_key: str) -> str:
    proc = subprocess.run(
        ["cast", "wallet", "address", "--private-key", normalize_word(private_key)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return normalize_hex(proc.stdout.strip(), word=True)


def cast_wallet_signature(private_key: str, digest: str) -> tuple[str, str, str]:
    proc = subprocess.run(
        [
            "cast",
            "wallet",
            "sign",
            "--private-key",
            normalize_word(private_key),
            "--no-hash",
            normalize_word(digest),
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    raw = normalize_hex(proc.stdout.strip())[2:]
    if len(raw) != 130:
        raise SystemExit(f"unexpected cast signature length: 0x{raw}")
    r = normalize_word("0x" + raw[:64])
    s = normalize_word("0x" + raw[64:128])
    v = normalize_word("0x" + raw[128:130])
    return v, r, s


def load_manifest(path: Path) -> dict[str, Any]:
    with path.open("rb") as f:
        return tomllib.load(f)


def suite_root(manifest: dict[str, Any], suite_id: str) -> Path:
    checkout_root = ROOT / manifest.get("checkout_root", ".foundry-suites")
    for suite in manifest.get("suite", []):
        if suite.get("id") != suite_id:
            continue
        if suite.get("kind") == "local":
            return ROOT / suite["path"]
        return checkout_root / suite_id
    raise SystemExit(f"unknown suite {suite_id!r}")


def suite_entry(manifest: dict[str, Any], suite_id: str) -> dict[str, Any]:
    for suite in manifest.get("suite", []):
        if suite.get("id") == suite_id:
            return suite
    raise SystemExit(f"unknown suite {suite_id!r}")


def suite_forge_args(manifest: dict[str, Any], suite_id: str) -> list[str]:
    return [str(arg) for arg in suite_entry(manifest, suite_id).get("forge_args", [])]


def artifact_paths(suite: Path) -> list[Path]:
    return sorted(suite.glob("out/**/*.json"))


def load_artifact(suite: Path, contract: str) -> tuple[Path, dict[str, Any]]:
    candidates = artifact_paths(suite)
    matches: list[Path] = []
    for path in candidates:
        if path.name == f"{contract}.json":
            matches.append(path)
    if not matches:
        raise SystemExit(f"could not find artifact for contract {contract!r} under {suite / 'out'}")
    if len(matches) > 1:
        paths = "\n".join(str(path) for path in matches)
        raise SystemExit(f"multiple artifacts matched {contract!r}:\n{paths}")
    return matches[0], json.loads(matches[0].read_text())


def candidate_artifacts(suite: Path) -> list[tuple[Path, dict[str, Any]]]:
    out: list[tuple[Path, dict[str, Any]]] = []
    for path in artifact_paths(suite):
        try:
            artifact = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if no_arg_test_signatures(artifact):
            out.append((path, artifact))
    return out


def source_path_for_artifact(suite: Path, artifact_path: Path) -> Path | None:
    try:
        rel = artifact_path.relative_to(suite / "out")
    except ValueError:
        return None
    source_name = rel.parts[0]
    matches = [
        path for path in suite.rglob(source_name)
        if path.is_file()
        and ".git" not in path.parts
        and "out" not in path.relative_to(suite).parts
        and "lib" not in path.relative_to(suite).parts
    ]
    if not matches:
        matches = [
            path for path in suite.rglob(source_name)
            if path.is_file()
            and ".git" not in path.parts
            and "out" not in path.relative_to(suite).parts
        ]
    return matches[0] if matches else None


def source_has_cheatcodes(path: Path | None) -> bool:
    if path is None:
        return False
    try:
        return CHEATCODE_RE.search(path.read_text(errors="ignore")) is not None
    except OSError:
        return False


def function_signature(entry: dict[str, Any]) -> str:
    types = ",".join(input_["type"] for input_ in entry.get("inputs", []))
    return f"{entry['name']}({types})"


def selectors(artifact: dict[str, Any]) -> dict[str, str]:
    method_ids = artifact.get("methodIdentifiers", {})
    out: dict[str, str] = {}
    for entry in artifact.get("abi", []):
        if entry.get("type") != "function":
            continue
        sig = function_signature(entry)
        selector = method_ids.get(sig)
        if selector is None:
            selector = cast_sig(sig)
        out[sig] = normalize_hex(selector)
    return out


def cast_sig(signature: str) -> str:
    proc = subprocess.run(
        ["cast", "sig", signature],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return proc.stdout.strip()


def no_arg_test_signatures(artifact: dict[str, Any]) -> list[str]:
    sigs: list[str] = []
    for entry in artifact.get("abi", []):
        if entry.get("type") != "function":
            continue
        name = entry.get("name", "")
        if not (name.startswith("test") or name.startswith("invariant")):
            continue
        if entry.get("inputs"):
            continue
        sigs.append(function_signature(entry))
    return sorted(sigs)


def extract_json_object(raw: str) -> dict[str, Any]:
    start = raw.find("{")
    end = raw.rfind("}")
    if start < 0 or end < start:
        raise ValueError("no JSON object in forge output")
    return json.loads(raw[start : end + 1])


def forge_gas(test_result: dict[str, Any]) -> int | None:
    kind = test_result.get("kind")
    if not isinstance(kind, dict):
        return None
    unit = kind.get("Unit")
    if isinstance(unit, dict) and isinstance(unit.get("gas"), int):
        return int(unit["gas"])
    fuzz = kind.get("Fuzz")
    if isinstance(fuzz, dict):
        median = fuzz.get("median_gas")
        if isinstance(median, int):
            return int(median)
    return None


def forge_expectations(
    suite: Path,
    forge_args: list[str],
    contract_label: str,
    timeout: float,
    *,
    match_test: str | None = None,
) -> dict[str, ForgeExpectation]:
    cmd = [
        "forge",
        "test",
        *forge_args,
        "--match-contract",
        f"^{re.escape(contract_label)}$",
    ]
    if match_test is not None:
        cmd += ["--match-test", f"^{re.escape(match_test)}$"]
    cmd.append("--json")
    try:
        proc = subprocess.run(
            cmd,
            cwd=suite,
            text=True,
            capture_output=True,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise UnsupportedReplay(f"Forge comparison timed out after {timeout:g}s") from exc
    try:
        data = extract_json_object(proc.stdout)
    except (json.JSONDecodeError, ValueError) as exc:
        message = proc.stderr.strip() or proc.stdout.strip() or str(exc)
        raise UnsupportedReplay(f"Forge comparison produced no parseable JSON: {message}") from exc

    matches = [
        value for key, value in data.items()
        if isinstance(value, dict) and key.endswith(f":{contract_label}")
    ]
    if not matches and len(data) == 1:
        only = next(iter(data.values()))
        if isinstance(only, dict):
            matches = [only]
    if not matches:
        raise UnsupportedReplay(f"Forge comparison found no contract result for {contract_label}")

    out: dict[str, ForgeExpectation] = {}
    for contract_result in matches:
        test_results = contract_result.get("test_results", {})
        if not isinstance(test_results, dict):
            continue
        for sig, test_result in test_results.items():
            if not isinstance(test_result, dict):
                continue
            reason = str(test_result.get("reason", ""))
            if sig.startswith("testFail") and "`testFail*` has been removed" in reason:
                continue
            status = str(test_result.get("status", "Unknown"))
            out[sig] = ForgeExpectation(status=status, gas=forge_gas(test_result))
    return out


def forge_expectations_for_tests(
    suite: Path,
    forge_args: list[str],
    contract_label: str,
    tests: list[str],
    timeout: float,
) -> tuple[dict[str, ForgeExpectation], str | None]:
    blocker: str | None = None
    try:
        expectations = forge_expectations(suite, forge_args, contract_label, timeout)
    except UnsupportedReplay as exc:
        expectations = {}
        blocker = str(exc)

    missing = [
        sig for sig in tests
        if sig not in expectations and not sig.startswith("testFail")
    ]
    for sig in missing:
        try:
            expectations.update(
                forge_expectations(
                    suite,
                    forge_args,
                    contract_label,
                    timeout,
                    match_test=sig,
                )
            )
        except UnsupportedReplay:
            continue
    if expectations or all(sig.startswith("testFail") for sig in tests):
        return expectations, None
    return expectations, blocker


def abi_bool(output_hex: str) -> bool | None:
    raw = normalize_hex(output_hex)[2:]
    if len(raw) < 64:
        return None
    return int(raw[-64:], 16) != 0


def unsupported_reason(result: dict[str, Any]) -> str | None:
    evm_error = str(result.get("evm_error", ""))
    if "unsupportedCheatcode" in evm_error:
        return evm_error
    return None


def parse_lean(stdout: str) -> dict[str, Any]:
    result: dict[str, Any] = {
        "storage": {},
        "account_storage": {},
        "account_balance": {},
        "account_nonce": {},
        "account_code": {},
        "account_destroyed": {},
    }
    for line in stdout.splitlines():
        parts = line.strip().split()
        if not parts:
            continue
        tag = parts[0]
        if tag == "storage" and len(parts) == 3:
            result["storage"][normalize_hex(parts[1], word=True)] = normalize_hex(parts[2], word=True)
        elif tag == "account_storage" and len(parts) == 4:
            address = normalize_hex(parts[1], word=True)
            key = normalize_hex(parts[2], word=True)
            result["account_storage"][(address, key)] = normalize_hex(parts[3], word=True)
        elif tag == "account_balance" and len(parts) == 3:
            result["account_balance"][normalize_hex(parts[1], word=True)] = normalize_hex(parts[2], word=True)
        elif tag == "account_nonce" and len(parts) == 3:
            result["account_nonce"][normalize_hex(parts[1], word=True)] = normalize_hex(parts[2], word=True)
        elif tag == "account_code" and len(parts) == 3:
            result["account_code"][normalize_hex(parts[1], word=True)] = normalize_hex(parts[2])
        elif tag == "account_destroyed" and len(parts) == 3:
            result["account_destroyed"][normalize_hex(parts[1], word=True)] = parts[2] == "1"
        elif len(parts) >= 2:
            result[tag] = " ".join(parts[1:])
    result["raw"] = stdout
    return result


def find_missing_hash(stdout: str) -> str | None:
    match = MISSING_HASH_RE.search(stdout)
    if not match:
        return None
    values = ast.literal_eval(match.group(1))
    return "0x" + "".join(f"{int(value) & 0xff:02x}" for value in values)


def find_missing_cheat_addr(stdout: str) -> str | None:
    match = MISSING_CHEAT_ADDR_RE.search(stdout)
    if not match:
        return None
    return normalize_word(match.group(1))


def find_missing_cheat_sign(stdout: str) -> tuple[str, str] | None:
    match = MISSING_CHEAT_SIGN_RE.search(stdout)
    if not match:
        return None
    return normalize_word(match.group(1)), normalize_word(match.group(2))


def lean_exe() -> str:
    built = ROOT / ".lake" / "build" / "bin" / "evm_parity"
    if built.exists():
        return str(built)
    return str(Path.home() / ".elan" / "bin" / "lake")


def lean_command(world: World, calldata: str, gas: int, fuel: int) -> list[str]:
    root = world.accounts[normalize_hex(world.root, word=True)]
    exe = lean_exe()
    if exe.endswith("/lake"):
        cmd = [exe, "exe", "evm_parity", "--"]
    else:
        cmd = [exe]
    cmd += [
        "--code",
        root.code,
        "--calldata",
        calldata,
        "--gas",
        str(gas),
        "--fuel",
        str(fuel),
        "--call-depth",
        "32",
        "--address",
        world.root,
        "--caller",
        CALLER,
        "--origin",
        ORIGIN,
        "--balance",
        word_to_short_hex(root.balance),
        "--nonce",
        word_to_short_hex(root.nonce),
    ]
    for key, value in sorted(root.storage.items()):
        cmd += ["--storage", f"{key}={value}", "--original-storage", f"{key}={value}"]
    root_word = normalize_hex(world.root, word=True)
    for address, account in sorted(world.accounts.items()):
        if address == root_word:
            continue
        cmd += ["--account", f"{address}={account.code}"]
        cmd += ["--account-balance", f"{address}={word_to_short_hex(account.balance)}"]
        cmd += ["--account-nonce", f"{address}={word_to_short_hex(account.nonce)}"]
        for key, value in sorted(account.storage.items()):
            cmd += ["--account-storage", f"{address}:{key}={value}"]
            cmd += ["--account-original-storage", f"{address}:{key}={value}"]
    for data, digest in sorted(world.keccak.items()):
        cmd += ["--keccak", f"{data}={digest}"]
    for private_key, address in sorted(world.cheat_addrs.items()):
        cmd += ["--cheat-addr", f"{private_key}={address}"]
    for (private_key, digest), (v, r, s) in sorted(world.cheat_signs.items()):
        cmd += ["--cheat-sign", f"{private_key}:{digest}={v}:{r}:{s}"]
    return cmd


def apply_result(world: World, result: dict[str, Any]) -> World:
    accounts: dict[str, AccountState] = {}
    account_addresses = set(result["account_balance"]) | set(result["account_nonce"]) | set(result["account_code"])
    for address in account_addresses:
        if result["account_destroyed"].get(address, False):
            continue
        account = AccountState(
            code=result["account_code"].get(address, "0x"),
            balance=result["account_balance"].get(address, "0x" + "0" * 64),
            nonce=result["account_nonce"].get(address, "0x" + "0" * 64),
        )
        accounts[address] = account
    for (address, key), value in result["account_storage"].items():
        accounts.setdefault(address, AccountState()).storage[key] = value
    return World(
        world.root,
        accounts,
        dict(world.keccak),
        dict(world.cheat_addrs),
        dict(world.cheat_signs),
    )


def run_call(
    world: World,
    calldata: str,
    gas: int,
    fuel: int,
    timeout: float,
) -> tuple[dict[str, Any], World]:
    attempts = 0
    while True:
        attempts += 1
        try:
            proc = subprocess.run(
                lean_command(world, calldata, gas, fuel),
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as exc:
            raise UnsupportedReplay(f"Lean call timed out after {timeout:g}s") from exc
        if proc.returncode != 0:
            sys.stderr.write(proc.stdout)
            sys.stderr.write(proc.stderr)
            raise SystemExit(proc.returncode)
        result = parse_lean(proc.stdout)
        missing = find_missing_hash(proc.stdout)
        if missing and missing not in world.keccak:
            if attempts > 200:
                raise SystemExit("too many missing-hash oracle iterations")
            world.keccak[missing] = cast_keccak(missing)
            continue
        missing_addr = find_missing_cheat_addr(proc.stdout)
        if missing_addr and missing_addr not in world.cheat_addrs:
            if attempts > 200:
                raise SystemExit("too many missing-cheat-addr oracle iterations")
            world.cheat_addrs[missing_addr] = cast_wallet_address(missing_addr)
            continue
        missing_sign = find_missing_cheat_sign(proc.stdout)
        if missing_sign and missing_sign not in world.cheat_signs:
            if attempts > 200:
                raise SystemExit("too many missing-cheat-sign oracle iterations")
            world.cheat_signs[missing_sign] = cast_wallet_signature(*missing_sign)
            continue
        if result.get("success") == "1":
            return result, apply_result(world, result)
        return result, world


def initial_world(runtime_code: str, *, initial_balance: int, initial_nonce: int) -> World:
    root_word = normalize_hex(TARGET, word=True)
    hevm_word = normalize_hex(HEVM_ADDRESS, word=True)
    return World(
        TARGET,
        {
            root_word: AccountState(
                code=normalize_hex(runtime_code),
                balance=str(initial_balance),
                nonce=str(initial_nonce),
            ),
            hevm_word: AccountState(code="0x00", nonce="1"),
        },
    )


def replay_artifact(
    artifact_path: Path,
    artifact: dict[str, Any],
    args: argparse.Namespace,
    *,
    contract_label: str,
    forge_expectations: dict[str, ForgeExpectation] | None = None,
    forge_blocker: str | None = None,
) -> tuple[int, int, int, int]:
    sels = selectors(artifact)
    runtime = artifact["deployedBytecode"]["object"]
    if not runtime:
        raise SystemExit(f"{artifact_path}: missing deployedBytecode.object")

    tests = no_arg_test_signatures(artifact)
    if args.match:
        tests = [sig for sig in tests if args.match in sig]
    if args.limit is not None:
        tests = tests[: args.limit]
    setup_selector = sels.get("setUp()")
    failed_selector = sels.get("failed()")

    passed = 0
    failed = 0
    unsupported = 0
    setup_blocker: str | None = None
    setup_world: World | None = None

    if forge_blocker is not None:
        for sig in tests:
            print(f"UNSUPPORTED {sig}: {forge_blocker}", flush=True)
        print(f"summary contract={contract_label} artifact={artifact_path}", flush=True)
        print(f"passed=0 failed=0 unsupported={len(tests)} total={len(tests)}", flush=True)
        return 0, 0, len(tests), len(tests)

    if setup_selector and tests:
        base_world = initial_world(
            runtime,
            initial_balance=args.initial_balance,
            initial_nonce=args.initial_nonce,
        )
        try:
            setup_result, setup_world = run_call(
                base_world, setup_selector, args.gas, args.fuel, args.call_timeout
            )
        except UnsupportedReplay as exc:
            setup_blocker = str(exc)
        else:
            if reason := unsupported_reason(setup_result):
                setup_blocker = reason
            elif setup_result.get("success") != "1":
                setup_blocker = f"failed with status {setup_result.get('status')}"
    elif tests:
        setup_world = initial_world(
            runtime,
            initial_balance=args.initial_balance,
            initial_nonce=args.initial_nonce,
        )

    for sig in tests:
        if (
            forge_expectations is not None
            and sig not in forge_expectations
            and not sig.startswith("testFail")
        ):
            print(f"UNSUPPORTED {sig}: Forge comparison has no result for this test", flush=True)
            unsupported += 1
            continue
        if setup_selector:
            if setup_blocker is not None:
                print(f"UNSUPPORTED {sig}: setUp {setup_blocker}", flush=True)
                unsupported += 1
                continue
        if setup_world is None:
            print(f"UNSUPPORTED {sig}: no initial world was available", flush=True)
            unsupported += 1
            continue
        world = clone_world(setup_world)
        try:
            result, after_test_world = run_call(world, sels[sig], args.gas, args.fuel, args.call_timeout)
        except UnsupportedReplay as exc:
            print(f"UNSUPPORTED {sig}: {exc}", flush=True)
            unsupported += 1
            continue
        if reason := unsupported_reason(result):
            print(f"UNSUPPORTED {sig}: {reason}", flush=True)
            unsupported += 1
            continue
        expected_revert = sig.startswith("testFail")
        failed_flag = False
        if result.get("success") == "1" and failed_selector:
            try:
                failed_result, _ = run_call(
                    after_test_world, failed_selector, args.gas, args.fuel, args.call_timeout
                )
            except UnsupportedReplay as exc:
                print(f"UNSUPPORTED {sig}: failed() check {exc}", flush=True)
                unsupported += 1
                continue
            if reason := unsupported_reason(failed_result):
                print(f"UNSUPPORTED {sig}: failed() check {reason}", flush=True)
                unsupported += 1
                continue
            if failed_result.get("success") != "1":
                print(
                    f"UNSUPPORTED {sig}: failed() check failed with status {failed_result.get('status')}",
                    flush=True,
                )
                unsupported += 1
                continue
            failed_value = abi_bool(str(failed_result.get("output", "0x")))
            if failed_value is None:
                print(f"UNSUPPORTED {sig}: failed() returned malformed output", flush=True)
                unsupported += 1
                continue
            failed_flag = failed_value
        lean_ok = (
            (result.get("success") != "1")
            or failed_flag
            if expected_revert
            else (result.get("success") == "1" and not failed_flag)
        )
        expectation = forge_expectations.get(sig) if forge_expectations is not None else None
        gas_ok = True
        gas_note = ""
        if expectation is not None:
            ok = lean_ok == expectation.ok
            if args.compare_gas and expectation.gas is not None and result.get("success") == "1":
                lean_gas = int(str(result.get("gas_used", "0")))
                gas_delta = abs(lean_gas - expectation.gas)
                gas_ok = gas_delta <= args.gas_tolerance
                gas_note = f" forge_gas={expectation.gas} lean_gas={lean_gas} gas_delta={gas_delta}"
            ok = ok and gas_ok
        else:
            ok = lean_ok
        if ok:
            if args.show_passes:
                forge_note = (
                    f" forge_status={expectation.status}"
                    if expectation is not None
                    else ""
                )
                print(f"PASS {sig}{forge_note}{gas_note}", flush=True)
            else:
                print(f"PASS {sig}", flush=True)
            passed += 1
        else:
            forge_note = (
                f" forge_status={expectation.status}"
                if expectation is not None
                else ""
            )
            print(
                f"FAIL {sig}: status={result.get('status')} "
                f"success={result.get('success')} failed_flag={int(failed_flag)}"
                f" lean_ok={int(lean_ok)}{forge_note}{gas_note}",
                flush=True,
            )
            if args.verbose_fail:
                for key in (
                    "gas_error",
                    "evm_error",
                    "cheat_prank",
                    "output",
                    "gas_used",
                    "gas_remaining",
                    "refund",
                ):
                    print(f"  {key}={result.get(key)}", flush=True)
            failed += 1
    print(f"summary contract={contract_label} artifact={artifact_path}", flush=True)
    print(f"passed={passed} failed={failed} unsupported={unsupported} total={len(tests)}", flush=True)
    return passed, failed, unsupported, len(tests)


def replay(args: argparse.Namespace) -> None:
    manifest = load_manifest(args.manifest)
    suite = suite_root(manifest, args.suite)
    forge_args = suite_forge_args(manifest, args.suite)

    if args.all:
        totals = [0, 0, 0, 0]
        contracts = 0
        skipped = 0
        for artifact_path, artifact in candidate_artifacts(suite):
            source_path = source_path_for_artifact(suite, artifact_path)
            if args.skip_cheatcode_contracts and source_has_cheatcodes(source_path):
                skipped += 1
                continue
            contract_label = artifact_path.stem
            if args.match_contract and args.match_contract not in contract_label:
                continue
            if any(pattern in contract_label for pattern in args.exclude_contract):
                skipped += 1
                continue
            contracts += 1
            print(f"\n== {contract_label} ==", flush=True)
            expectations = None
            forge_blocker = None
            if args.compare_forge:
                tests = no_arg_test_signatures(artifact)
                if args.match:
                    tests = [sig for sig in tests if args.match in sig]
                if args.limit is not None:
                    tests = tests[: args.limit]
                expectations, forge_blocker = forge_expectations_for_tests(
                    suite, forge_args, contract_label, tests, args.forge_timeout
                )
            passed, failed, unsupported, total = replay_artifact(
                artifact_path,
                artifact,
                args,
                contract_label=contract_label,
                forge_expectations=expectations,
                forge_blocker=forge_blocker,
            )
            totals[0] += passed
            totals[1] += failed
            totals[2] += unsupported
            totals[3] += total
            if failed and args.stop_on_failure:
                break
        print(
            f"\nsuite_summary suite={args.suite} contracts={contracts} skipped_contracts={skipped} "
            f"passed={totals[0]} failed={totals[1]} unsupported={totals[2]} total={totals[3]}",
            flush=True,
        )
        if totals[1]:
            raise SystemExit(1)
        return

    if not args.contract:
        raise SystemExit("--contract is required unless --all is used")
    artifact_path, artifact = load_artifact(suite, args.contract)
    expectations = None
    forge_blocker = None
    if args.compare_forge:
        tests = no_arg_test_signatures(artifact)
        if args.match:
            tests = [sig for sig in tests if args.match in sig]
        if args.limit is not None:
            tests = tests[: args.limit]
        expectations, forge_blocker = forge_expectations_for_tests(
            suite, forge_args, args.contract, tests, args.forge_timeout
        )
    passed, failed, unsupported, total = replay_artifact(
        artifact_path,
        artifact,
        args,
        contract_label=args.contract,
        forge_expectations=expectations,
        forge_blocker=forge_blocker,
    )
    if failed:
        raise SystemExit(1)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--suite", required=True)
    parser.add_argument("--contract")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--match-contract")
    parser.add_argument("--exclude-contract", action="append", default=[])
    parser.add_argument("--match")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--skip-cheatcode-contracts", action="store_true")
    parser.add_argument("--stop-on-failure", action="store_true")
    parser.add_argument("--verbose-fail", action="store_true")
    parser.add_argument("--show-passes", action="store_true")
    parser.add_argument("--compare-forge", action="store_true")
    parser.add_argument("--compare-gas", action="store_true")
    parser.add_argument("--gas-tolerance", type=int, default=0)
    parser.add_argument("--gas", type=int, default=DEFAULT_GAS)
    parser.add_argument("--fuel", type=int, default=DEFAULT_FUEL)
    parser.add_argument("--call-timeout", type=float, default=120.0)
    parser.add_argument("--forge-timeout", type=float, default=60.0)
    parser.add_argument("--initial-balance", type=lambda raw: int(raw, 0), default=DEFAULT_INITIAL_BALANCE)
    parser.add_argument("--initial-nonce", type=lambda raw: int(raw, 0), default=DEFAULT_INITIAL_NONCE)
    parser.set_defaults(func=replay)
    return parser


def main() -> None:
    args = build_parser().parse_args()
    args.func(args)


if __name__ == "__main__":
    main()

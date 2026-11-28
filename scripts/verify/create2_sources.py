#!/usr/bin/env python3
"""Writes and tests the frontend's translation of inline assembly create2 (Contracts/Create2).

    scripts/verify/create2_sources.py [--solc SOLC] [--check]

Writes Contracts/Create2/Source.lean, the frontend's translation of Contracts/Create2/Deployer.sol,
and Contracts/Create2/SourceView.lean, the same with `deploy` declared `view` (which solc rejects
before it writes an AST, so the mutation is made on the translation): SolidCore's checker must
reject it (Contracts/Create2/Run.lean). Then checks that the frontend rejects every other inline
assembly block of the negative cases below. With --check, compares instead of writing and exits 1
on a difference or on a case the frontend does not decide as expected.
"""

import argparse
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
FRONTEND = ROOT / "scripts" / "solc_ast_to_lean_source.py"
DIR = ROOT / "Contracts" / "Create2"
NAMESPACE = "SolidCore.Verify.Create2.Source"
VIEW_NAMESPACE = "SolidCore.Verify.Create2.SourceView"

# (name, function body): each block is outside the one create2 shape, so the frontend fails.
NEGATIVE = [
    ("offset 64", "assembly { a := create2(0, add(code, 64), mload(code), salt) }"),
    ("create", "assembly { a := create(0, add(code, 32), mload(code)) }"),
    ("length of another local", "bytes memory other = code; assembly { a := create2(0, add(code, 32), mload(other), salt) }"),
    ("two statements", "assembly { a := create2(0, add(code, 32), mload(code), salt) a := 0 }"),
    ("Yul local", "assembly { let s := salt a := create2(0, add(code, 32), mload(code), s) }"),
    ("bytes16 salt", "bytes16 s = bytes16(salt); assembly { a := create2(0, add(code, 32), mload(code), s) }"),
    ("uint8 value", "uint8 v = 0; assembly { a := create2(v, add(code, 32), mload(code), salt) }"),
    ("value expression", "assembly { a := create2(callvalue(), add(code, 32), mload(code), salt) }"),
    ("memory target", "bytes memory b; assembly { b := create2(0, add(code, 32), mload(code), salt) }"),
    ("uint256 target", "uint256 w; assembly { w := create2(0, add(code, 32), mload(code), salt) }"),
]
NEGATIVE_SOURCE = """// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Negative {
    function f(bytes32 salt) external returns (address a) {
        bytes memory code = hex"00";
        BODY
    }
}
"""


HEAD = "import SolidCore.Solidity.Checked\nimport SolidCore.Witness.Checked\n"


def translate(solc: str, sol: pathlib.Path, contract: str, namespace: str) -> subprocess.CompletedProcess:
    out = subprocess.run(
        [sys.executable, str(FRONTEND), "--solc", solc, "--contract", contract, "--namespace", namespace,
         str(sol)], cwd=ROOT, capture_output=True, text=True)
    if out.returncode == 0:
        # As scripts/verify/uniswap_v2_sources.py: the checker's import only, the frontend's
        # opens, and the source's path relative to the repository.
        if not out.stdout.startswith(HEAD):
            sys.exit("error: unexpected frontend header")
        out.stdout = ("import SolidCore.Solidity.Checked\n\nopen SolidCore.Solidity\n"
                      + out.stdout[len(HEAD):].replace(str(ROOT) + "/", ""))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solc", default="solc")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    status = 0
    sol = (DIR / "Deployer.sol").relative_to(ROOT)
    out = translate(a.solc, sol, "Deployer", NAMESPACE)
    if out.returncode != 0:
        print(out.stderr, file=sys.stderr)
        return 1
    source = out.stdout
    out = translate(a.solc, sol, "Deployer", VIEW_NAMESPACE)
    if out.returncode != 0:
        print(out.stderr, file=sys.stderr)
        return 1
    view = out.stdout
    deploy = 'name := some "deploy",'
    old, new = "mutability := StateMutability.nonpayable", "mutability := StateMutability.view"
    if view.count(deploy) != 1:
        sys.exit("error: expected one deploy function")
    j = view.index(old, view.index(deploy))
    view = view[:j] + new + view[j + len(old):]
    header = ("-- Generated from Contracts/Create2/Deployer.sol with solc 0.8.35 by "
              "scripts/verify/create2_sources.py. Do not edit.\n\n")
    for name, text in (("Source.lean", header + source), ("SourceView.lean", header + view)):
        path = DIR / name
        if a.check:
            if not path.exists() or path.read_text() != text:
                print(f"error: {path.relative_to(ROOT)} is out of date", file=sys.stderr)
                status = 1
        else:
            path.write_text(text)
    with tempfile.TemporaryDirectory() as tmp:
        for name, body in NEGATIVE:
            neg = pathlib.Path(tmp) / "Negative.sol"
            neg.write_text(NEGATIVE_SOURCE.replace("BODY", body))
            compiled = subprocess.run([a.solc, "--ast-compact-json", str(neg)], capture_output=True, text=True)
            if compiled.returncode != 0:
                print(f"error: negative case {name!r} does not compile:\n{compiled.stderr}", file=sys.stderr)
                status = 1
                continue
            res = translate(a.solc, neg, "Negative", "X")
            if res.returncode == 0 or "assembly" not in res.stderr.lower():
                print(f"error: the frontend accepted negative case {name!r}", file=sys.stderr)
                status = 1
            else:
                print(f"rejected {name}: {res.stderr.strip().splitlines()[-1]}")
    return status


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Writes SolidCore's sources of the Uniswap V2 port (solar's solar-tv/uniswap-v2/port.py).

    scripts/verify/uniswap_v2_sources.py --port DIR [--solc SOLC] [--check]

SolidCore's frontend (scripts/solc_ast_to_lean_source.py) reads one file with no imports and no
inline assembly, so for each certified contract this writes one file (scripts/verify/uniswap-v2/
NAME.sol): the contract's file and every file it imports, in import order, each without its
`import` and `pragma solidity` lines, under one `pragma solidity ^0.8.0;`. One edit changes
code: `UniswapV2ERC20`'s constructor reads the chain ID as `block.chainid` instead of with
inline assembly `chainid()`, the same value (solc documents `block.chainid` as the `CHAINID`
opcode). Every edit must apply exactly once. solar's certified backend compiles the same file.
Then solc 0.8.35's AST of it goes through the frontend into Contracts/UniswapV2/C/Source.lean.
With --check, compares instead of writing and exits 1 on a difference.

v2-core is GPL-3.0, so, as in solar, this repository keeps the recipe and not the code: the
`.sol` and `Source.lean` files are ignored by git and generated before the build, from the
output of solar's solar-tv/uniswap-v2/port.py (v2-core 6a9e7c9).
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
OUT_SOL = ROOT / "scripts" / "verify" / "uniswap-v2"
FRONTEND = ROOT / "scripts" / "solc_ast_to_lean_source.py"
# (contract, its file in the port, the Lean directory under Contracts/UniswapV2, the functions
# the translation leaves out). `UniswapV2Factory.createPair` deploys the pair with inline
# assembly `create2` of `type(UniswapV2Pair).creationCode`, outside SolidCore's fragment, so
# SolidCore's Factory has no `createPair` and nothing proved of it covers that function.
CONTRACTS = [
    ("UniswapV2ERC20", "UniswapV2ERC20.sol", "ERC20", []),
    ("UniswapV2Pair", "UniswapV2Pair.sol", "Pair", []),
    ("UniswapV2Factory", "UniswapV2Factory.sol", "Factory", ["UniswapV2Factory.createPair"]),
]
CHAINID_OLD = """        assembly {
            chainId := chainid()
        }"""
CHAINID_NEW = "        chainId = block.chainid;"
IMPORT = re.compile(r"^import\s+['\"]([^'\"]+)['\"];\n", re.M)


def flatten(port: pathlib.Path, main: str) -> str:
    order: list[pathlib.Path] = []

    def visit(p: pathlib.Path) -> None:
        p = p.resolve()
        if p in order:
            return
        for m in IMPORT.finditer(p.read_text()):
            visit(p.parent / m.group(1))
        order.append(p)

    visit(port / main)
    parts = []
    for p in order:
        text = p.read_text()
        text = IMPORT.sub("", text)
        text = re.sub(r"^pragma solidity [^;]+;\n", "", text, flags=re.M)
        text = re.sub(r"^// SPDX-License-Identifier:[^\n]*\n", "", text, flags=re.M)
        parts.append(f"// {p.relative_to(port.resolve())}\n{text.strip()}\n")
    flat = "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\n\n" + "\n".join(parts)
    if flat.count(CHAINID_OLD) != 1:
        sys.exit("error: the chain ID assembly occurs more than once")
    return flat.replace(CHAINID_OLD, CHAINID_NEW)


def lean_of(solc: str, sol: pathlib.Path, contract: str, omit: list[str]) -> str:
    rel = sol.relative_to(ROOT)
    out = subprocess.run(
        [sys.executable, str(FRONTEND), "--solc", solc, "--contract", contract,
         "--namespace", f"SolidCore.Verify.VC.Source.{contract}", str(rel)]
        + [f"--omit-function={f}" for f in omit],
        cwd=ROOT, check=True, capture_output=True, text=True).stdout
    head = "import SolidCore.Solidity.Checked\nimport SolidCore.Witness.Checked\n"
    if not out.startswith(head):
        sys.exit("error: unexpected frontend header")
    left_out = f", without {', '.join(omit)}" if omit else ""
    return (f"-- Generated from {rel} (the Uniswap V2 port's {contract}, flattened{left_out}) with "
            "solc 0.8.35 by scripts/verify/uniswap_v2_sources.py. Do not edit.\n\n"
            "import SolidCore.Solidity.Checked\n\nopen SolidCore.Solidity\n" + out[len(head):])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=pathlib.Path, required=True)
    ap.add_argument("--solc", default="solc")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    status = 0
    OUT_SOL.mkdir(parents=True, exist_ok=True)

    def put(path: pathlib.Path, text: str) -> None:
        nonlocal status
        if a.check:
            if not path.exists() or path.read_text() != text:
                print(f"error: {path.relative_to(ROOT)} is out of date", file=sys.stderr)
                status = 1
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    for contract, main_file, d, omit in CONTRACTS:
        sol = OUT_SOL / f"{contract}.sol"
        put(sol, flatten(a.port, main_file))
        if not a.check:
            put(ROOT / "Contracts" / "UniswapV2" / d / "Source.lean", lean_of(a.solc, sol, contract, omit))
    return status


if __name__ == "__main__":
    sys.exit(main())


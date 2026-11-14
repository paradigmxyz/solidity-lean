#!/usr/bin/env python3
"""Writes SolidCore's source and checked contract of one source mutant of UniswapV2ERC20.

    scripts/verify/uniswap_v2_mutant.py --solc SOLC --sol MUTANT.sol --name M --out DIR

MUTANT.sol is the flattened port (scripts/verify/uniswap-v2/UniswapV2ERC20.sol) with one edit
(scripts/verify/uniswap_v2_transfer_slice.sh applies it). Writes DIR/Source.lean, the frontend's
translation (namespace SolidCore.Verify.VC.Source.UniswapV2ERC20Mut<M>), and DIR/Core.lean,
scripts/verify/uniswap_v2_core.py's checked contract of it (namespace
SolidCore.Verify.VC.UniswapV2ERC20Mut<M>: contract_ok, fuel, the selector and topic tables).
Nothing here is trusted: both are checked by the kernel when they build. Derived from the GPL-3.0
port, so not committed.
"""

import argparse
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts" / "verify"))
import uniswap_v2_core as core  # noqa: E402
import uniswap_v2_sources as sources  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solc", required=True)
    ap.add_argument("--sol", type=pathlib.Path, required=True)
    ap.add_argument("--name", required=True)
    ap.add_argument("--out", type=pathlib.Path, required=True)
    a = ap.parse_args()
    c = "UniswapV2ERC20"
    m = f"{c}Mut{a.name}"
    sol = a.sol.resolve()
    out = a.out.resolve()
    mod = ".".join(out.relative_to(ROOT).parts)
    src = sources.lean_of(a.solc, sol, c, [])
    # The frontend opens the namespace one component a line: rename the innermost one.
    for old, new in [(f"namespace {c}\n", f"namespace {m}\n"), (f"end {c}\n", f"end {m}\n")]:
        if src.count(old) != 1:
            sys.exit(f"error: {old!r} is not in the frontend's output exactly once")
        src = src.replace(old, new)
    text = core.render(c, "ERC20", *core.signatures(a.solc, sol))
    for old, new in [
        ("import Contracts.UniswapV2.ERC20.Source", f"import {mod}.Source"),
        (f"SolidCore.Verify.VC.Source.{c}.", f"SolidCore.Verify.VC.Source.{m}."),
        (f"SolidCore.Verify.VC.{c}", f"SolidCore.Verify.VC.{m}"),
    ]:
        if old not in text:
            sys.exit(f"error: {old!r} not in the rendered Core")
        text = text.replace(old, new)
    out.mkdir(parents=True, exist_ok=True)
    (out / "Source.lean").write_text(src)
    (out / "Core.lean").write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())

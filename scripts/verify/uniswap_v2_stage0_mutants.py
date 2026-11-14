#!/usr/bin/env python3
"""Writes three mutants of the exported stage0 of UniswapV2ERC20 for the negative controls of
Contracts/UniswapV2/ERC20/Nested/NegE3.lean (generated, not committed, as Stage0.lean is):

  Mut1  _approve's SSTORE of allowance[owner][spender] dropped;
  Mut2  _approve hashes the owner into mapping slot 3 instead of 2 (allowance's slot);
  Mut3  transferFrom's SSTORE of the spent allowance dropped.

Each edit must apply exactly once inside its function, else exit 1.

    scripts/verify/uniswap_v2_stage0_mutants.py
"""
import pathlib, sys

d = pathlib.Path("Certified/uv2_erc20/gen/UniswapV2ERC20")
src = (d / "Stage0.lean").read_text()


def fn_span(text, name):
    i = text.index(f"    -- @{name}\n")
    j = text.index("    -- @", i + 1)
    return i, j


def mutate(text, fn, old, new):
    i, j = fn_span(text, fn)
    body = text[i:j]
    if body.count(old) != 1:
        sys.exit(f"mutant: {old!r} occurs {body.count(old)} times in @{fn}")
    return text[:i] + body.replace(old, new) + text[j:]


muts = {
    "Mut1": ("_approve", "         .effect none .sstore [.value 23, .value 2],\n", ""),
    "Mut2": ("_approve", ".effect none .mstore [.const 32, .const 2],", ".effect none .mstore [.const 32, .const 3],"),
    "Mut3": ("transferFrom", ",\n         .effect none .sstore [.value 75, .value 20]]", "]"),
}
for name, (fn, old, new) in muts.items():
    t = mutate(src, fn, old, new)
    t = t.replace("namespace SolarTV.Export.UniswapV2ERC20\n", f"namespace SolarTV.Export.UniswapV2ERC20{name}\n")
    t = t.replace("end SolarTV.Export.UniswapV2ERC20\n", f"end SolarTV.Export.UniswapV2ERC20{name}\n")
    if f"namespace SolarTV.Export.UniswapV2ERC20{name}" not in t:
        sys.exit("mutant: namespace not found")
    (d / f"Stage0{name}.lean").write_text(t)
    print(f"wrote {d}/Stage0{name}.lean")

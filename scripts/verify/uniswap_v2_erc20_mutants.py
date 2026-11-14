#!/usr/bin/env python3
"""Write mutants of solar's exported stage0 of UniswapV2ERC20 for the negative controls of
Contracts/UniswapV2/ERC20/SourceMirNeg.lean: each edits one instruction of transfer, _transfer or
SafeMath's sub and must change the file (else this fails), under its own namespace
SolarTV.Export.UniswapV2ERC20Mut.<name>. Derived from the GPL-3.0 port, so not committed.

  python3 scripts/verify/uniswap_v2_erc20_mutants.py Certified/uv2_erc20/gen
"""
import re, sys, pathlib

gen = pathlib.Path(sys.argv[1])
src = (gen / "UniswapV2ERC20" / "Stage0.lean").read_text()

def block(text, name):
    """The span of function @name's entry in the exported module."""
    start = text.index(f"    -- @{name}\n")
    nxt = text.find("    -- @", start + 1)
    return start, (nxt if nxt != -1 else len(text))

def edit(fn, old, new, count=1):
    def f(text):
        a, b = block(text, fn)
        body = text[a:b]
        if body.count(old) < count:
            raise SystemExit(f"mutant: {old!r} not found {count}x in @{fn}")
        return text[:a] + body.replace(old, new, count) + text[b:]
    return f

# name -> (edit, what it breaks)
MUTANTS = {
    "NoDebit": (edit("_transfer", ".effect none .sstore [.value 36, .value 7],\n", ""),
                "the debit of balanceOf[from] dropped"),
    "WrongSlot": (edit("_transfer", ".effect none .mstore [.const 32, .const 1],", ".effect none .mstore [.const 32, .const 2],"),
                  "balanceOf's slot 1 read as slot 2"),
    "NoOverflowCheck": (edit("_transfer", ".pure 26 .lt [.value 25, .value 14]", ".pure 26 .gt [.value 25, .value 14]"),
                        "the add overflow test reversed"),
    "NoUnderflowCheck": (edit("sub", ".pure 3 .lt [.value 0, .value 2]", ".pure 3 .gt [.value 0, .value 2]"),
                         "SafeMath sub's underflow test reversed"),
    "WrongTopic": (edit("_transfer", "0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef", "0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ee"),
                   "the Transfer topic changed"),
    "WrongReturn": (edit("transfer", ".effect none .mstore [.const 0, .const 1]", ".effect none .mstore [.const 0, .const 0]"),
                    "returns false"),
    "WrongRevertData": (edit("_transfer", "0x64732d6d6174682d6164642d6f766572666c6f77", "0x64732d6d6174682d6164642d6f766572666c6f78"),
                        "the add overflow revert reason changed"),
    "SwappedLogArgs": (edit("_transfer", ".value 0, .value 1]]", ".value 1, .value 0]]"),
                       "from and to swapped in the Transfer topics"),
}

out = gen / "UniswapV2ERC20Mut"
out.mkdir(parents=True, exist_ok=True)
for name, (f, _) in MUTANTS.items():
    text = f(src)
    if text == src:
        raise SystemExit(f"mutant {name} did not change stage0")
    text = text.replace("namespace SolarTV.Export.UniswapV2ERC20\n", f"namespace SolarTV.Export.UniswapV2ERC20Mut.{name}\n", 1)
    text = text.replace("end SolarTV.Export.UniswapV2ERC20\n", f"end SolarTV.Export.UniswapV2ERC20Mut.{name}\n", 1)
    if f"namespace SolarTV.Export.UniswapV2ERC20Mut.{name}" not in text or f"end SolarTV.Export.UniswapV2ERC20Mut.{name}" not in text:
        raise SystemExit(f"mutant {name}: namespace not rewritten")
    (out / f"{name}.lean").write_text(text)
print(" ".join(MUTANTS))


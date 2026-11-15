#!/usr/bin/env python3
"""Mutants of a UniswapV2Pair stage set (scripts/verify/uniswap_v2_pair_stages.sh NEGATIVES=1).

    python3 scripts/verify/uniswap_v2_pair_mutants.py NAME

From Certified/NAME/gen writes Certified/NAMEneg/gen (getReserves' 32-bit timestamp mask 0xffffffff
made 0xfffffff in the first MIR pass's output, mir1, where it must appear exactly once in
getReserves, and every PUSH4 0xffffffff of the final EVM IR) and Certified/NAMEnegb/gen (the first
PUSH4 0xffffffff of the runtime bytecode made 0x0fffffff, the stages unchanged). Generated, never
committed.
"""
import json, pathlib, re, shutil, sys

name = sys.argv[1]
root = pathlib.Path(__file__).resolve().parents[2] / "Certified"
src = root / name / "gen" / "UniswapV2Pair"
neg, negb = root / f"{name}neg", root / f"{name}negb"
for d in (neg, negb):
    shutil.rmtree(d, ignore_errors=True)
    (d / "gen").mkdir(parents=True)
    shutil.copytree(src, d / "gen" / "UniswapV2Pair")


def edit_between(path, start, stop, old, new):
    t = path.read_text()
    i = t.index(start)
    j = t.index(stop, i + len(start))
    body = t[i:j]
    assert body.count(old) == 1, (path, old)
    path.write_text(t[:i] + body.replace(old, new) + t[j:])


g = neg / "gen" / "UniswapV2Pair"
edit_between(g / "Mir1.lean", "-- @getReserves\n", "-- @", ".const 0xffffffff]", ".const 0xfffffff]")
last = [s["file"] for s in json.loads((g / "manifest.json").read_text())["stages"] if s["pass"] != "assemble"][-1]
t = (g / last).read_text()
assert t.count("(.push 0xffffffff)") >= 1, last
(g / last).write_text(t.replace("(.push 0xffffffff)", "(.push 0xfffffff)"))

p = negb / "gen" / "UniswapV2Pair" / "Bytecode.lean"
t = p.read_text()
hx = re.search(r'def bytecodeHex : String :=\n  "([0-9a-f]+)"', t).group(1)
# The first PUSH4 0xffffffff at an instruction boundary (walking the opcodes and PUSH immediates).
code = bytes.fromhex(hx)
pc, k = 0, None
while pc < len(code):
    op = code[pc]
    if op == 0x63 and code[pc + 1:pc + 5] == b"\xff" * 4:
        k = 2 * pc
        break
    pc += 1 + (op - 0x5F if 0x60 <= op <= 0x7F else 0)
assert k is not None
hx2 = hx[:k] + "630fffffff" + hx[k + 10:]
byte = k // 2 + 1
head = "def bytecode : List Nat :=\n  ["
i = t.index(head) + len(head)
j = t.index("]", i)
items = [x.strip() for x in t[i:j].split(",")]
assert int(items[byte], 16) == 0xFF
items[byte] = "0x0f"
body = ",\n   ".join(", ".join(items[n:n + 16]) for n in range(0, len(items), 16))
p.write_text((t[:i] + body + t[j:]).replace(hx, hx2))
print(f"mutants: {neg.name} (mir1, {last[:-5].lower()}), {negb.name} (bytecode byte {byte})")

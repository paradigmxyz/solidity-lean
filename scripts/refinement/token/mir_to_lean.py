#!/usr/bin/env python3
"""Transcribe solar's printed lowered MIR (after lower-evm-shaped) into a SolarTV Lean module.

    scripts/refinement/token/mir_to_lean.py STAGE.mir NAMESPACE > Stage0.lean

The input is one module as solar -Zprint-after-each prints it after lower-evm-shaped. The
output follows the layout of solar's -Zemit-lean-stages: the functions in the printed order
with the dispatch entry last, blocks by their bbN number, EVM operand order for shifts, each
function's parameters as fresh value numbers past the module's largest, and !metadata dropped.
An instruction it does not know stops it with an error rather than a guess.
"""
import re
import sys

PURE = {"add", "sub", "mul", "div", "lt", "gt", "eq", "and", "or", "xor", "byte", "iszero", "not"}
SHIFT = {"shl", "shr"}
EFFECT0 = {"calldatasize", "callvalue", "caller"}


def die(msg):
    sys.exit(f"error: {msg}")


def parse(text):
    fns = []
    cur = None
    blk = None
    for raw in text.splitlines():
        line = raw.split(";", 1)[0].rstrip()
        line = re.sub(r"\s*!metadata\((?:[^()]|\([^()]*\))*\)", "", line)
        if not line.strip() or line.startswith("@"):
            continue
        m = re.match(r"fn @(\w+)\((.*?)\)(?:\s*->\s*[^\s\[{]+)?(\s*\[[^\]]*\])?\s*\{", line)
        if m:
            params = [p.split(":")[0].strip() for p in m.group(2).split(",") if p.strip()]
            cur = {"name": m.group(1), "params": params, "blocks": {}, "entry": "entry" in (m.group(3) or "")}
            fns.append(cur)
            continue
        if line.strip() == "}":
            cur = None
            continue
        m = re.match(r"\s*bb(\d+)(?:\s*\[[^\]]*\])?:", line)
        if m:
            blk = {"insts": []}
            cur["blocks"][int(m.group(1))] = blk
            continue
        blk["insts"].append(line.strip())
    return fns


def main():
    text = open(sys.argv[1]).read()
    ns = sys.argv[2]
    fns = parse(text)
    order = [f for f in fns if not f["entry"]] + [f for f in fns if f["entry"]]
    index = {f["name"]: i for i, f in enumerate(order)}
    top = max(int(v) for v in re.findall(r"\bv(\d+)\b", text))
    nxt = top + 1
    out = []
    for f in order:
        argmap = {}
        for p in f["params"]:
            argmap[p] = nxt
            nxt += 1

        def opd(tok):
            tok = tok.strip()
            if re.fullmatch(r"v\d+", tok):
                return f".value {tok[1:]}"
            if tok in argmap:
                return f".value {argmap[tok]}"
            if re.fullmatch(r"0x[0-9a-fA-F]+|\d+", tok):
                return f".const {tok}"
            die(f"operand {tok}")

        def dst(tok):
            tok = tok.split(":")[0].strip()
            if not re.fullmatch(r"v\d+", tok):
                die(f"destination {tok}")
            return tok[1:]

        nums = sorted(f["blocks"])
        if nums != list(range(len(nums))):
            die(f"the blocks of @{f['name']} are not bb0..bbN")
        blocks = []
        for b in nums:
            insts, term = [], None
            for ins in f["blocks"][b]["insts"]:
                if term is not None:
                    die(f"an instruction after the terminator in @{f['name']} bb{b}: {ins}")
                m = re.fullmatch(r"(v\d+(?::\s*\w+)?)\s*=\s*(.*)", ins)
                if m:
                    d, rhs = dst(m.group(1)), m.group(2)
                    mz = re.fullmatch(r"zext i\d+ (\S+) to i256", rhs)
                    if mz:
                        insts.append(f".word {d} ({opd(mz.group(1))})")
                        continue
                    op, _, rest = rhs.partition(" ")
                    args = [a for a in rest.split(",") if a.strip()]
                    if op == "ne":
                        insts.append(f".ne {d} ({opd(args[0])}) ({opd(args[1])})")
                    elif op in PURE:
                        insts.append(f".pure {d} .{op} [{', '.join(opd(a) for a in args)}]")
                    elif op in SHIFT:
                        insts.append(f".pure {d} .{op} [{opd(args[1])}, {opd(args[0])}]")
                    elif op in EFFECT0 and not args:
                        insts.append(f".effect (some {d}) .{op} []")
                    elif op in ("calldataload", "sload", "keccak256"):
                        insts.append(f".effect (some {d}) .{op} [{', '.join(opd(a) for a in args)}]")
                    elif op == "icall":
                        callee = args[0].strip().lstrip("@")
                        insts.append(f".call (some {d}) {index[callee]} [{', '.join(opd(a) for a in args[1:])}]")
                    else:
                        die(f"the instruction {ins}")
                    continue
                op, _, rest = ins.partition(" ")
                args = [a for a in rest.split(",") if a.strip()]
                if op in ("mstore", "sstore"):
                    insts.append(f".effect none .{op} [{', '.join(opd(a) for a in args)}]")
                elif op == "log":
                    insts.append(f".effect none (.log {len(args) - 2}) [{', '.join(opd(a) for a in args)}]")
                elif op == "jumpi":
                    term = f".branch ({opd(args[0])}) {args[1].strip()[2:]} {args[2].strip()[2:]}"
                elif op == "jump":
                    term = f".jump {args[0].strip()[2:]}"
                elif op == "returndata":
                    term = f".ret ({opd(args[0])}) ({opd(args[1])})"
                elif op == "revert":
                    term = f".revert ({opd(args[0])}) ({opd(args[1])})"
                elif op == "stop":
                    term = ".stop"
                elif op == "tail_call":
                    callee = args[0].strip().lstrip("@")
                    term = f".tailCall {index[callee]} [{', '.join(opd(a) for a in args[1:])}]"
                elif op == "switch":
                    m = re.fullmatch(r"switch (\S+), default bb(\d+), \[(.*)\]", ins)
                    cases = [c.split("=>") for c in m.group(3).split(",")]
                    cs = ", ".join(f"({opd(k)}, {t.strip()[2:]})" for k, t in cases)
                    term = f".switch ({opd(m.group(1))}) {m.group(2)} [{cs}]"
                else:
                    die(f"the instruction {ins}")
            if term is None:
                die(f"@{f['name']} bb{b} has no terminator")
            body = ",\n         ".join(insts)
            blocks.append(f"      -- bb{b}\n      ⟨[],\n        [{body}],\n        {term}⟩")
        params = ", ".join(str(argmap[p]) for p in f["params"])
        out.append(f"    -- @{f['name']}\n    {{ params := [{params}],\n      blocks := [\n"
                   + ",\n".join(blocks) + "] }")
    bt = chr(96)
    print("import SolarTV.MIR.Program")
    print()
    print("/-! Transcribed by scripts/refinement/token/mir_to_lean.py from solar's lowered MIR after")
    print(f"{bt}lower-evm-shaped{bt} (scripts/refinement/token/stage0.mir); do not edit. -/")
    print()
    print(f"namespace {ns}")
    print()
    print("open SolarTV")
    print()
    print(f"/-- The first lowered MIR module, after {bt}lower-evm-shaped{bt} advanced the phase. -/")
    print("def stage0 : MIR.Lowered.Module :=")
    print(f"  {{ entry := {len(order) - 1},")
    print("    functions := [")
    print(",\n".join(out) + "] }")
    print()
    print(f"end {ns}")


main()

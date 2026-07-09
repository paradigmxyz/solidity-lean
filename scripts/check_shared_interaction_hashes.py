#!/usr/bin/env python3
"""Guarantee the interaction alphabet stays single-sourced.

Since 2026-07-09, evm-compiler consumes the `evm-interaction` package directly:
its `EvmCompiler/Simulation/{Interaction,OpenWorld,Outcome}.lean` are re-export
stubs (`import EvmInteraction.Simulation.X` and nothing else), and the real
sources live only in `../evm-interaction/EvmInteraction/Simulation/`. The old
byte-identity check between two live copies is obsolete; this script now
asserts single-sourcing instead:
  * each evm-compiler stub contains exactly one import of the package module
    and NO declarations (def/theorem/structure/inductive/class/instance);
  * each package source file exists and is non-trivial.
Reads both sibling repos read-only. Exit 0 iff single-sourced.
"""

from __future__ import annotations
import re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
EC = HERE.parent / "evm-compiler" / "EvmCompiler" / "Simulation"
EI = HERE.parent / "evm-interaction" / "EvmInteraction" / "Simulation"
DECL = re.compile(r"^\s*(def|theorem|structure|inductive|class|instance|abbrev|opaque|axiom)\b")

ok = True
for name in ["Interaction", "OpenWorld", "Outcome"]:
    stub = EC / f"{name}.lean"
    src = EI / f"{name}.lean"
    if not src.exists() or len(src.read_text()) < 1000:
        print(f"FAIL: package source missing/trivial: {src}", file=sys.stderr); ok = False
        continue
    text = stub.read_text() if stub.exists() else ""
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)  # strip block comments
    text = "\n".join(l for l in text.splitlines() if not l.strip().startswith("--"))
    imports = [l for l in text.splitlines() if l.startswith("import ")]
    if imports != [f"import EvmInteraction.Simulation.{name}"] or any(DECL.match(l) for l in text.splitlines()):
        print(f"FAIL: {stub} is not a pure re-export stub of the package module", file=sys.stderr); ok = False

if ok:
    print("single-source OK: evm-compiler stubs re-export the evm-interaction package; no duplicate alphabet sources.")
sys.exit(0 if ok else 1)

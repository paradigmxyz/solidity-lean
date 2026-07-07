#!/usr/bin/env python3
"""BC soundness-audit probe driver (audit artifact — not wired into manifest).

Usage:
  drive.py accept <sol> <Contract>       -> solc accept/reject vs our import+typecheck accept/reject
  drive.py eval   <sol> <Contract> <expr...>  -> import + run given #eval exprs (our side values)

Prints machine-readable lines. Ground truth solc: pinned 0.8.35.
"""
from __future__ import annotations
import json, os, subprocess, sys, tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SOLC = os.environ.get("SOLC", "/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35")
IMPORTER = REPO / "scripts" / "solc_ast_to_lean_source.py"


def solc_compile(sol: Path) -> tuple[bool, str]:
    """Full compile to bytecode (matches harness --bin) so codegen-level checks fire."""
    p = subprocess.run([SOLC, "--bin", str(sol)], text=True, capture_output=True)
    if p.returncode != 0 or "Error" in p.stderr:
        return False, (p.stderr or p.stdout)
    return True, ""


def our_import(sol: Path, contract: str, ns: str) -> tuple[bool, str, str]:
    p = subprocess.run([sys.executable, str(IMPORTER), str(sol), "--contract", contract,
                        "--solc", SOLC, "--namespace", ns, "--body-only"],
                       text=True, capture_output=True)
    if p.returncode != 0:
        return False, "", (p.stderr or p.stdout)
    return True, p.stdout, ""


def run_lean(imports: list[str], body: str, evals: list[str]) -> tuple[int, str, str]:
    opens = ("open SolidCore.Solidity SolidCore.Solidity.Source "
             "SolidCore.Solidity.TypeCheck SolidCore.Solidity.TypeCheck.Examples "
             "SolidCore.Solidity.TypeCheck.CheckedInput "
             "SolidCore.Solidity.SolcAstImport.Probe")
    lines = [f"import {i}" for i in imports] + ["", body, "", opens]
    for e in evals:
        lines.append(f"#eval {e}")
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir="/tmp") as f:
        f.write("\n".join(lines) + "\n")
        path = f.name
    p = subprocess.run(["lake", "env", "lean", path], cwd=REPO, text=True, capture_output=True)
    return p.returncode, p.stdout, p.stderr


def cmd_accept(sol: str, contract: str):
    solp = Path(sol)
    ok, err = solc_compile(solp)
    print(f"SOLC: {'ACCEPT' if ok else 'REJECT'}")
    if not ok:
        print("  " + err.strip().replace("\n", "\n  ")[:600])
    imp_ok, body, imperr = our_import(solp, contract, "SolidCore.Solidity.SolcAstImport.Probe")
    if not imp_ok:
        print("OURS: REJECT (import failure)")
        print("  " + imperr.strip().replace("\n", "\n  ")[:600])
        return
    rc, out, serr = run_lean(["SolidCore.Solidity.Checked", "SolidCore.Witness.Checked"],
                             body, ["SolidCore.Solidity.SolcAstImport.Probe.importedContractAccepted"])
    if rc != 0:
        print("OURS: LEAN-ERROR")
        print("  " + (serr or out).strip().replace("\n", "\n  ")[:800])
        return
    val = [l for l in out.splitlines() if l.strip()]
    print(f"OURS: {'ACCEPT' if val and val[-1].strip()=='true' else 'REJECT (typecheck)'}  raw={val[-1] if val else '?'}")


def cmd_eval(sol: str, contract: str, exprs: list[str]):
    solp = Path(sol)
    ok, err = solc_compile(solp)
    print(f"SOLC: {'ACCEPT' if ok else 'REJECT'}")
    if not ok:
        print("  " + err.strip().replace("\n", "\n  ")[:400])
    imp_ok, body, imperr = our_import(solp, contract, "SolidCore.Solidity.SolcAstImport.Probe")
    if not imp_ok:
        print("OURS: REJECT (import failure)")
        print("  " + imperr.strip().replace("\n", "\n  ")[:600])
        return
    rc, out, serr = run_lean(["SolidCore.Solidity.Checked", "SolidCore.Witness.Checked"],
                             body, ["SolidCore.Solidity.SolcAstImport.Probe.importedContractAccepted"] + exprs)
    if rc != 0:
        print("OURS: LEAN-ERROR")
        print("  " + (serr or out).strip().replace("\n", "\n  ")[:1200])
        return
    for l in [l for l in out.splitlines() if l.strip()]:
        print("  EVAL: " + l)


if __name__ == "__main__":
    if len(sys.argv) < 4:
        print(__doc__); sys.exit(2)
    mode = sys.argv[1]
    if mode == "accept":
        cmd_accept(sys.argv[2], sys.argv[3])
    elif mode == "eval":
        cmd_eval(sys.argv[2], sys.argv[3], sys.argv[4:])
    else:
        print(__doc__); sys.exit(2)

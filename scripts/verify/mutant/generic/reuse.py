#!/usr/bin/env python3
"""reuse.py DRIVER_DIR FRESH_RECORD_DIR FRESH_EXIT CASE_DIR: run the driver's own replay_main
(tools/certify/generic.py, imported unchanged) on CASE_DIR, with its one cold run replaced by an
existing fresh run's record directory.

replay_main checks CASE_DIR's run files against its record.json, starts the fresh cold run with
subprocess.run, and then compares REPLAY_KEYS between the record and the fresh run's record.json.
The fresh run reads only the source, the spec kind, the tier, the base and the contract, never the
pins a pin-layer case changes. So one fresh run serves every pin case: this stands in for that one
subprocess.run call. It copies FRESH_RECORD_DIR to the --record-dir replay_main asked for and
returns FRESH_EXIT. Everything else, the verdict line and the exit, is replay_main's own. This is
the driver comparison reused on one fresh run, not an independent driver run per case."""
import argparse, importlib.util, shutil, subprocess, sys

ap = argparse.ArgumentParser()
ap.add_argument("driver")
ap.add_argument("fresh")
ap.add_argument("fresh_exit", type=int)
ap.add_argument("case")
a = ap.parse_args()

spec = importlib.util.spec_from_file_location("generic", f"{a.driver}/tools/certify/generic.py")
g = importlib.util.module_from_spec(spec)
sys.argv = [spec.origin]
spec.loader.exec_module(g)
real = subprocess.run
calls = []


def fake_run(cmd, *args, **kw):
    if "--record-dir" in cmd and not calls:
        calls.append(cmd)
        rd = cmd[cmd.index("--record-dir") + 1]
        print(f"== reuse: fresh run {a.fresh} (exit {a.fresh_exit}) as {rd}", flush=True)
        shutil.copytree(a.fresh, rd)
        return subprocess.CompletedProcess(cmd, a.fresh_exit)
    return real(cmd, *args, **kw)


g.subprocess.run = fake_run
g.replay_main(argparse.Namespace(replay=a.case, solidity_lean="/nonexistent", work=None, packages_from=None, probe_cache=None))

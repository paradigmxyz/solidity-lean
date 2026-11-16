# Replays a run directory with DRIVER's generic.replay_main unchanged, its fresh run replaced by the
# published fresh run of acc4-flag's replay (no Lean): checks only, not a full replay.
import argparse, contextlib, io, json, pathlib, shutil, subprocess, sys
driver, d, fresh = sys.argv[1], pathlib.Path(sys.argv[2]).resolve(), pathlib.Path(sys.argv[3])
sys.path.insert(0, f"{driver}/tools/certify")
import generic
def fake(cmd, *a, **k):
    out = pathlib.Path(cmd[cmd.index("--record-dir") + 1]); out.mkdir(parents=True)
    shutil.copy(fresh, out / "record.json"); return subprocess.CompletedProcess(cmd, 0)
generic.subprocess.run = fake
buf = io.StringIO()
try:
    with contextlib.redirect_stdout(buf):
        generic.replay_main(argparse.Namespace(replay=str(d), work=str(d.parent / "w"), solidity_lean="/nonexistent", packages_from=None, probe_cache=None))
except SystemExit as e:
    print(f"exit={e.code} :: {buf.getvalue().strip().splitlines()[-1][:200]}")

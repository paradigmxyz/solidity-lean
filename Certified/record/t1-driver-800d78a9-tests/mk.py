import hashlib, json, pathlib, shutil, sys
src = pathlib.Path(sys.argv[1]); N = "flag_4ce5cf9a"
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rehash(d, rel):
    r = json.loads((d / "record.json").read_text()); r["run_files"][rel] = h(d / rel); return r
def save(d, r): (d / "record.json").write_text(json.dumps(r, indent=2) + "\n")
def input_rehashed(d):
    f = d / f"inputs/Certified/{N}/Source.lean"; f.write_text(f.read_text() + "-- edited after the run\n")
    save(d, rehash(d, f"inputs/Certified/{N}/Source.lean"))
def shape_rehashed(d):
    f = d / f"inputs/Certified/{N}/shape.json"; t = f.read_text(); assert "fun _ => 3580203" in t
    f.write_text(t.replace("fun _ => 3580203", "fun _ => 1790101")); save(d, rehash(d, f"inputs/Certified/{N}/shape.json"))
def caveats_forged(d):
    c = json.loads((d / "certify-record.json").read_text()); c["caveats"] = []
    (d / "certify-record.json").write_text(json.dumps(c, indent=2) + "\n")
    r = rehash(d, "certify-record.json"); r["caveats"] = []; save(d, r)
for n, f in [("control", None), ("input-rehashed", input_rehashed), ("shape-rehashed", shape_rehashed), ("caveats-forged-consistent", caveats_forged)]:
    d = pathlib.Path(n) / "replay"; shutil.copytree(src, d)
    if f: f(d)

# Edit one archived run file (append a Lean comment) and rehash only its run_files entry.
import json,sys,hashlib,pathlib
d=pathlib.Path(sys.argv[1]); rel=sys.argv[2]
f=d/rel; f.write_text(f.read_text()+chr(10)+"-- edited after the run"+chr(10))
rp=d/"record.json"; r=json.loads(rp.read_text()); assert rel in r["run_files"]
r["run_files"][rel]=hashlib.sha256(f.read_bytes()).hexdigest(); rp.write_text(json.dumps(r,indent=2)+chr(10))

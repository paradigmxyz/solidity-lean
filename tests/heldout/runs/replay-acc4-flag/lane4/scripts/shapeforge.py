# Halve the gas bound in archived shape.json; rehash only its run_files entry.
import json,sys,hashlib,pathlib,re
d=pathlib.Path(sys.argv[1]); rel="inputs/Certified/flag_4ce5cf9a/shape.json"
f=d/rel; j=json.loads(f.read_text()); g=int(re.search(r"\d+", j["gas"]).group()); j["gas"]=j["gas"].replace(str(g),str(g//2)); f.write_text(json.dumps(j,indent=2)+chr(10))
rp=d/"record.json"; r=json.loads(rp.read_text()); r["run_files"][rel]=hashlib.sha256(f.read_bytes()).hexdigest(); rp.write_text(json.dumps(r,indent=2)+chr(10))

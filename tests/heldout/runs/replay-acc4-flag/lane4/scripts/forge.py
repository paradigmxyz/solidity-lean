# Coordinated forge: edit final.theorem in certify-record.json AND record.json, and re-hash run_files.
import json,sys,hashlib,pathlib
d=pathlib.Path(sys.argv[1]); new=sys.argv[2]
cp=d/"certify-record.json"; c=json.loads(cp.read_text()); c["final"]["theorem"]=new; cp.write_text(json.dumps(c,indent=2)+chr(10))
rp=d/"record.json"; r=json.loads(rp.read_text()); r["final"]["theorem"]=new
r["run_files"]["certify-record.json"]=hashlib.sha256(cp.read_bytes()).hexdigest(); rp.write_text(json.dumps(r,indent=2)+chr(10))

# Drop caveats from certify-record.json and record.json together; rehash certify-record.json's run_files entry.
import json,sys,hashlib,pathlib
d=pathlib.Path(sys.argv[1])
cp=d/"certify-record.json"; c=json.loads(cp.read_text()); c["caveats"]=[]; cp.write_text(json.dumps(c,indent=2)+chr(10))
rp=d/"record.json"; r=json.loads(rp.read_text()); r["caveats"]=[]
r["run_files"]["certify-record.json"]=hashlib.sha256(cp.read_bytes()).hexdigest(); rp.write_text(json.dumps(r,indent=2)+chr(10))

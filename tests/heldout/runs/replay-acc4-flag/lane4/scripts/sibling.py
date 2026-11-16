# Sibling leakage tampers on a replay/ copy.
# pin: swap lower()'s and raise(uint256)'s selectors in record.json functions and in certify-record.json
#      (certify-record.json rehashed in run_files), so the record pairs each proof with its sibling's selector.
# input: point shape.json's raise(uint256) entry at lower()'s lowered function (fn0), rehash only its run_files entry.
import json,sys,hashlib,pathlib
d=pathlib.Path(sys.argv[1]); mode=sys.argv[2]
rp=d/"record.json"; r=json.loads(rp.read_text())
def swap(fs):
    a=[f for f in fs if f["signature"]=="lower()"][0]; b=[f for f in fs if f["signature"]=="raise(uint256)"][0]
    a["selector"],b["selector"]=b["selector"],a["selector"]
if mode=="pin":
    swap(r["functions"])
    cp=d/"certify-record.json"; c=json.loads(cp.read_text())
    if isinstance(c.get("functions"),list): swap(c["functions"])
    cp.write_text(json.dumps(c,indent=2)+chr(10)); r["run_files"]["certify-record.json"]=hashlib.sha256(cp.read_bytes()).hexdigest()
else:
    rel="inputs/Certified/flag_4ce5cf9a/shape.json"; f=d/rel; j=json.loads(f.read_text())
    [e for e in j["entries"] if e["signature"]=="raise(uint256)"][0]["fn"]="Certified.flag_4ce5cf9a.Lowering.fn0"
    f.write_text(json.dumps(j,indent=2)+chr(10)); r["run_files"][rel]=hashlib.sha256(f.read_bytes()).hexdigest()
rp.write_text(json.dumps(r,indent=2)+chr(10))

import json,sys
p=sys.argv[1]; r=json.load(open(p)); exec(sys.argv[2]); open(p,'w').write(json.dumps(r,indent=2)+chr(10))

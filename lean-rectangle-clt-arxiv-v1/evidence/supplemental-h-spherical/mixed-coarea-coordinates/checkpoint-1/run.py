#!/usr/bin/env python3
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess
root = Path(__file__).resolve().parents[4]
out = root / "evidence/supplemental-h-spherical/mixed-coarea-coordinates/checkpoint-1"
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p): return hashlib.sha256((root / p).read_bytes()).hexdigest()
def save(p,x): p.write_text(json.dumps(x,indent=2)+"\n")
owned = ["RectangleCLTArxivV1/SupplementalHMixedCoareaCoordinates.lean"]
seen=set()
def visit(p):
    if p in seen: return
    seen.add(p)
    for m in re.findall(r"^import\s+(RectangleCLTArxivV1\.[\w.]+)",(root/p).read_text(),re.M):
        visit(m.replace(".","/")+".lean")
for p in owned: visit(p)
files=sorted(seen)+["lakefile.toml","lake-manifest.json","lean-toolchain","source-pins.json"]
files += [str((out / n).relative_to(root)) for n in ["Audit.lean","run.py","targets.json"]]
freeze={p:sha(p) for p in files}
save(out/"source-freeze.json",{"created_at":now(),"sha256":freeze})
r={"started_at":now(),"scope":"actual signed conditional pair section and exact native Gaussian density Gram-Jacobian conversion","source_sha256":freeze,"checked_target_count":json.loads((out/"targets.json").read_text())["target_count"],"commands":[]}
save(out/"receipt.json",r)
commands=[("build",["lake","build","RectangleCLTArxivV1.SupplementalHMixedCoareaCoordinates"])]
commands += [("force-"+Path(p).stem,["lake","env","lean",p]) for p in owned]
commands += [("audit",["lake","env","lean",str((out/"Audit.lean").relative_to(root))])]
env=dict(os.environ);env["PATH"]="/workspace/lean-toolchain-bin/bin:"+env["PATH"]
for label,argv in commands:
    log=out/(label+".log");row={"label":label,"argv":argv,"cwd":str(root),"started_at":now(),"log":str(log.relative_to(root))}
    with log.open("w") as stream: result=subprocess.run(argv,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
    row.update(finished_at=now(),exit_code=result.returncode,log_sha256=sha(log.relative_to(root)));r["commands"].append(row);save(out/"receipt.json",r);print(label+": "+str(result.returncode),flush=True)
    if result.returncode:break
r["finished_at"]=now();r["source_unchanged"]=all(sha(p)==h for p,h in freeze.items());r["passed"]=len(r["commands"])==len(commands) and all(c["exit_code"]==0 for c in r["commands"]) and r["source_unchanged"];save(out/"receipt.json",r);print("PASS" if r["passed"] else "FAIL",flush=True)

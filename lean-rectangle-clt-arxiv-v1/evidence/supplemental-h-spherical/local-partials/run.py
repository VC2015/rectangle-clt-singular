#!/usr/bin/env python3
from pathlib import Path
import datetime,hashlib,json,os,subprocess
root=Path(__file__).resolve().parents[3]
out=root/'evidence/supplemental-h-spherical/local-partials'
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p): return hashlib.sha256((root/p).read_bytes()).hexdigest()
def save(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
files=['RectangleCLTArxivV1/SupplementalHLocalPartials.lean','lakefile.toml','lake-manifest.json','lean-toolchain','evidence/supplemental-h-spherical/local-partials/Audit.lean','evidence/supplemental-h-spherical/local-partials/run.py']
freeze={f:sha(f) for f in files}
save(out/'source-freeze.json',{'created_at':now(),'sha256':freeze})
receipt={'started_at':now(),'scope':'local genuine coordinate partials imply actual Frechet derivative','source_sha256':freeze,'checked_target_count':1,'commands':[]}
save(out/'receipt.json',receipt)
commands=[('build',['lake','build','RectangleCLTArxivV1.SupplementalHLocalPartials']),('force',['lake','env','lean','RectangleCLTArxivV1/SupplementalHLocalPartials.lean']),('audit',['lake','env','lean','evidence/supplemental-h-spherical/local-partials/Audit.lean'])]
env=dict(os.environ);env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
for label,argv in commands:
 log=out/(label+'.log'); row={'label':label,'argv':argv,'cwd':str(root),'started_at':now(),'log':str(log.relative_to(root))}
 with log.open('w') as stream: result=subprocess.run(argv,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
 row.update(finished_at=now(),exit_code=result.returncode,log_sha256=sha(log.relative_to(root)));receipt['commands'].append(row);save(out/'receipt.json',receipt);print(label+': '+str(result.returncode),flush=True)
 if result.returncode: break
receipt['finished_at']=now();receipt['source_unchanged']=all(sha(f)==h for f,h in freeze.items());receipt['passed']=len(receipt['commands'])==len(commands) and all(r['exit_code']==0 for r in receipt['commands']) and receipt['source_unchanged'];save(out/'receipt.json',receipt);print('PASS' if receipt['passed'] else 'FAIL',flush=True)

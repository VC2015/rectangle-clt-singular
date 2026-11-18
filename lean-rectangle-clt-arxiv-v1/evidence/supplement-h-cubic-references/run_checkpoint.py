from pathlib import Path
import json,hashlib,os,subprocess,datetime
P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
O=E/'checkpoint-1';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
modules=['SupplementalHCubicSigns', 'SupplementalHWeightedReference']
paths=[*[P/('RectangleCLTArxivV1/'+m+'.lean') for m in modules],*[E/x for x in ['Audit.lean','ExpandedTypes.lean','targets.json','run_checkpoint.py']]]
identity=lambda:{str(p.relative_to(P)):sha(p) for p in paths}
r={'scope':'Actual both-sign cubic projected references and intrinsic Gaussian-weighted one-face reference masses','source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'status':'running','initial_source_identity':identity(),'started_at':now(),'commands':[]}
receipt=O/'run.json'
def save():receipt.write_text(json.dumps(r,indent=2)+'\n')
def run(label,argv):
 log=O/(label+'.log');row={'label':label,'argv':argv,'started_at':now(),'log':str(log.relative_to(P))};r['commands'].append(row);save()
 print(label,flush=True)
 with log.open('wb') as f:ret=subprocess.run(argv,cwd=P,stdout=f,stderr=subprocess.STDOUT,env=os.environ.copy())
 row.update(exit_code=ret.returncode,finished_at=now(),log_sha256=sha(log));save();assert ret.returncode==0,(label,log)
 return log
try:
 run('build',['lake','build']+['RectangleCLTArxivV1.'+m for m in modules])
 
 for m in modules:run('force-'+m,['lake','env','lean','RectangleCLTArxivV1/'+m+'.lean','-o','.lake/build/lib/lean/RectangleCLTArxivV1/'+m+'.olean'])
 run('audit',['lake','env','lean',str((E/'Audit.lean').relative_to(P))])
 meta=json.loads(run('expanded-types',['lake','env','lean',str((E/'ExpandedTypes.lean').relative_to(P))]).read_text())
 (O/'expanded-types.json').write_text(json.dumps(meta,indent=2)+'\n')
 assert len(meta['endpoints'])==7
 r['final_source_identity']=identity();assert r['initial_source_identity']==r['final_source_identity']
 r.update(status='passed',finished_at=now(),audit_targets=7)
except Exception as e:r.update(status='failed',finished_at=now(),error=str(e));save();raise
save();print('PASS',receipt,flush=True)

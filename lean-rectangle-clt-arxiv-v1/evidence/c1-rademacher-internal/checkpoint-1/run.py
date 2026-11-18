import datetime,hashlib,json,os,subprocess
from pathlib import Path
P=Path(__file__).resolve().parents[3];D=Path(__file__).resolve().parent
cfg=json.loads((D/'config.json').read_text());files=[P/x for x in cfg['hash_files']]+[D/x for x in ['Audit.lean','Types.lean','targets.json','config.json','run.py']]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();identity=lambda:{str(p.relative_to(P)):sha(p) for p in files};now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
r={'scope':cfg['scope'],'release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'source_identity':identity(),'commands':[],'status':'running'}
def save():(D/'run.json').write_text(json.dumps(r,indent=2)+'\n')
def run(label,cmd):
 log=D/(label+'.log');row={'label':label,'argv':cmd,'cwd':str(P),'started_at_utc':now(),'log':str(log.relative_to(P))};r['commands'].append(row);save()
 with log.open('wb') as out:p=subprocess.run(cmd,cwd=P,env=os.environ,stdout=out,stderr=subprocess.STDOUT)
 row.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(log));save();assert p.returncode==0,label;print(label,'PASS',flush=True)
try:
 run('01-build',['lake','build','RectangleCLTArxivV1.RademacherBoundary'])
 for i,f in enumerate(cfg['force_files'],2):run(f'{i:02d}-force-'+Path(f).stem,['lake','env','lean',f])
 run('20-strict-audit',['lake','env','lean',str((D/'Audit.lean').relative_to(P))]);a=json.loads((D/'20-strict-audit.log').read_text());assert a['all_axioms_allowed'];r['strict_targets']=len(a['targets'])
 run('21-types-kernel-routes',['lake','env','lean',str((D/'Types.lean').relative_to(P))]);t=json.loads((D/'21-types-kernel-routes.log').read_text());r['expanded_types']=len(t['endpoints']);r['project_dependency_nodes']=len(t['project_dependency_graph'])
 assert identity()==r['source_identity'];r.update(status='passed',finished_at_utc=now(),source_identity_after=identity());save();print('Checkpoint PASS',flush=True)
except Exception as e:r.update(status='failed',finished_at_utc=now(),error=str(e));save();raise

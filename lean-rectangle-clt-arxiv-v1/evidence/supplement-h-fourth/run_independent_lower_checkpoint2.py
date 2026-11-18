import datetime,hashlib,json,os,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];BASE=Path(__file__).resolve().parent;OLD=BASE/'independent-lower-checkpoint-1';O=BASE/'independent-lower-checkpoint-2';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
old=json.loads((OLD/'run.json').read_text());assert old['status']=='failed' and old['error']=='types-and-strict-audit failed';assert all(c['exit_code']==0 for c in old['commands'][:-1]);assert 'unknown constant' in (OLD/'types-and-strict-audit.log').read_text()
sources=old['source_identity'];
for p,h in sources.items():assert sha(R/p)==h,p
s=(OLD/'TypesAndAudit.lean').read_text();imports=['HFourthSeededPhysicalBase','HFourthSeededScales','HFourthPhysicalMatrixTransport'];s=''.join('import RectangleCLTArxivV1.'+m+'\n' for m in imports)+s;s=s.replace('    ``RectangleCLTArxivV1.HFourthSeededMatrixEstimates,','    ``RectangleCLTArxivV1.HFourthSeededMatrixEstimates,\n    ``RectangleCLTArxivV1.HFourthSeededMatrixEstimates.mk,');(O/'TypesAndAudit.lean').write_text(s)
targets=old['strict_targets']+['RectangleCLTArxivV1.HFourthSeededMatrixEstimates.mk'];(O/'targets.json').write_text(json.dumps(targets,indent=2)+'\n')
r={'scope':'Independent complete93-target strict/full-type/dependency review for frozen downstream conditional H3/Cor4 assembly. All22 source forces already passed in checkpoint1; only its type-harness imports were incomplete. No proof source changed.','release_wide_certification':False,'source_commit':old['source_commit'],'source_identity':sources,'ledger_sha256':old['ledger_sha256'],'strict_targets':targets,'reused_successful_build_and_22_force_checks':{'receipt':str((OLD/'run.json').relative_to(R)),'sha256':sha(OLD/'run.json'),'overall_historical_status':'failed because of12 missing declarations in the type-harness import closure; successful build and22 source elaborations are reused at byte-identical hashes','successful_commands':[{'label':c['label'],'log':c['log'],'log_sha256':c['log_sha256']} for c in old['commands'][:-1]]},'status':'running','started_at_utc':now(),'commands':[]};rec=O/'run.json'
def save():rec.write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
def run(label,argv):
 c={'label':label,'argv':argv,'log':str((O/(label+'.log')).relative_to(R)),'started_at_utc':now()};r['commands'].append(c);save()
 with (R/c['log']).open('wb') as f:p=subprocess.run(argv,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
 c.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(R/c['log']));save()
 if p.returncode:raise RuntimeError(label+' failed')
try:
 save();run('build-complete-fixture-imports',['lake','build',*['RectangleCLTArxivV1.'+m for m in ['GapMain','HFourthAngleAssembly',*imports]]]);run('types-and-strict-audit',['lake','env','lean',str((O/'TypesAndAudit.lean').relative_to(R))]);d=json.loads(next(x for x in (O/'types-and-strict-audit.log').read_text().splitlines() if x.startswith('{')));(O/'expanded-types.json').write_text(json.dumps(d,indent=2)+'\n')
 for p,h in sources.items():assert sha(R/p)==h,p
 assert sha(R/'correspondence/supplemental-h-fourth-assembly-passages.json')==old['ledger_sha256'];r.update(status='passed',full_type_count=len(d['endpoints']),dependency_nodes=len(d['project_dependency_graph']),expanded_types_sha256=sha(O/'expanded-types.json'),finished_at_utc=now());save()
except Exception as e:r.update(status='failed',error=str(e),finished_at_utc=now());save();raise
print(json.dumps({k:r[k] for k in ['status','full_type_count','dependency_nodes']}))

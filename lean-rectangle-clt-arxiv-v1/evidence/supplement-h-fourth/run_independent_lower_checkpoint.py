import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];O=Path(__file__).resolve().parent/'independent-lower-checkpoint-1';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
L=json.loads((R/'correspondence/supplemental-h-fourth-assembly-passages.json').read_text()); sources={};targets=[]
for d in ['checkpoint-intermediate-1','checkpoint-seeded-model-1','checkpoint-comparison-1','checkpoint-angle-assembly-1']:
 x=json.loads((O.parent/d/'run.json').read_text());assert x['status']=='passed';sources.update(x['final_source_identity'])
 s=(O.parent/d/'Audit.lean').read_text();t=s.split('let targets := #[',1)[1].split(']\n',1)[0];targets+=re.findall(r'``([A-Za-z0-9_.]+)',t)
N='RectangleCLTArxivV1.'
extra=['HFourthSeededMatrixEstimates','HFourthSeededMatrixEstimates.cubic','HFourthSeededMatrixEstimates.pair','GapNormalizedMatrixEstimates']
targets=list(dict.fromkeys(targets+[N+n for n in extra]));s=(R/'evidence/early-correspondence/checkpoint-1/TypesAndAudit.lean').read_text();s=re.sub(r'^import RectangleCLTArxivV1.*\n','',s,flags=re.M);s='import RectangleCLTArxivV1.GapMain\nimport RectangleCLTArxivV1.HFourthAngleAssembly\n'+s;s=re.sub(r'let targets := #\[.*?\]\n  let mut queue','let targets := #[\n'+',\n'.join('    ``'+n for n in targets)+']\n  let mut queue',s,flags=re.S);s=s.replace('Fresh early passage correspondence: C1 bounded/Gaussian, Corollary1 normalization, Lemma2 actual endpoint smoothing; no q0 derivative correspondence claim','Independent conditional downstream H3/Cor4 assembly review; actual matrix suppliers remain explicit')
(O/'TypesAndAudit.lean').write_text(s);(O/'targets.json').write_text(json.dumps(targets,indent=2)+'\n')
for p,h in sources.items():assert sha(R/p)==h,p
r={'scope':'Independent fresh selected build and22-source force, strict3 full types/dependencies for conditional actual H3 finite derivative/restoration/seeded remainder/law transport/time comparison and Cor4 optimization. Only the actual matrix suppliers remain explicit; raw H3/Cor4 headline stays open.','release_wide_certification':False,'status':'running','source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'source_identity':sources,'ledger_sha256':sha(R/'correspondence/supplemental-h-fourth-assembly-passages.json'),'strict_targets':targets,'started_at_utc':now(),'commands':[]};rec=O/'run.json'
def save():rec.write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
def run(label,argv):
 z={'label':label,'argv':argv,'started_at_utc':now(),'log':str((O/(label+'.log')).relative_to(R))};r['commands'].append(z);save()
 with (R/z['log']).open('wb') as f:p=subprocess.run(argv,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
 z.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(R/z['log']));save()
 if p.returncode:raise RuntimeError(label+' failed')
try:
 save();run('build',['lake','build','RectangleCLTArxivV1.GapMain','RectangleCLTArxivV1.HFourthAngleAssembly'])
 for p in L['source_files']:run('force-'+Path(p).stem,['lake','env','lean',p])
 run('types-and-strict-audit',['lake','env','lean',str((O/'TypesAndAudit.lean').relative_to(R))]);x=json.loads(next(l for l in (O/'types-and-strict-audit.log').read_text().splitlines() if l.startswith('{')));(O/'expanded-types.json').write_text(json.dumps(x,indent=2)+'\n')
 for p,h in sources.items():assert sha(R/p)==h,p
 assert sha(R/'correspondence/supplemental-h-fourth-assembly-passages.json')==r['ledger_sha256']
 r.update(status='passed',full_type_count=len(x['endpoints']),dependency_nodes=len(x['project_dependency_graph']),expanded_types_sha256=sha(O/'expanded-types.json'),finished_at_utc=now());save()
except Exception as e:r.update(status='failed',error=str(e),finished_at_utc=now());save();raise
print(json.dumps({k:r[k] for k in ['status','full_type_count','dependency_nodes']}))

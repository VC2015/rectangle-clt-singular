from pathlib import Path
import json,re,hashlib,datetime,os,subprocess
R=Path(__file__).resolve().parents[2];O=Path(__file__).resolve().parent/'real-cutoff-checkpoint-1';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
targets=['RectangleCLTArxivV1.familyActivationCount_real_cutoff_event','RectangleCLTArxivV1.familyMaskedSignMaximum_all_active_bound_real']
s=(R/'evidence/early-correspondence/checkpoint-1/TypesAndAudit.lean').read_text();s=re.sub(r'^import RectangleCLTArxivV1.*\n','',s,flags=re.M);s='import RectangleCLTArxivV1.LowerAllActiveRealCutoff\n'+s;s=re.sub(r'let targets := #\[.*?\]\n  let mut queue','let targets := #[\n'+',\n'.join('    ``'+n for n in targets)+']\n  let mut queue',s,flags=re.S);(O/'TypesAndAudit.lean').write_text(s)
sources={p:sha(R/p) for p in ['RectangleCLTArxivV1/LowerAllActiveRealCutoff.lean','../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricFamilyAllActive.lean','../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricFamilyActivation.lean']}
r={'status':'running','scope':'Only the literal real-cutoff all-active bound derived from the preserved actual integer-count/natural-cutoff primitive; no new lower headline','release_wide_certification':False,'source_identity':sources,'targets':targets,'commands':[]}
def save():(O/'run.json').write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
try:
 save()
 for label,argv in [('build',['lake','build','RectangleCLTArxivV1.LowerAllActiveRealCutoff']),('force',['lake','env','lean','RectangleCLTArxivV1/LowerAllActiveRealCutoff.lean']),('types-and-strict-audit',['lake','env','lean',str((O/'TypesAndAudit.lean').relative_to(R))])]:
  x={'label':label,'argv':argv,'started_at_utc':now(),'log':str((O/(label+'.log')).relative_to(R))};r['commands'].append(x);save()
  with (R/x['log']).open('wb') as f:p=subprocess.run(argv,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  x.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(R/x['log']));save();assert p.returncode==0,label
 x=json.loads(next(l for l in (O/'types-and-strict-audit.log').read_text().splitlines() if l.startswith('{')));(O/'expanded-types.json').write_text(json.dumps(x,indent=2)+'\n')
 for p,h in sources.items():assert sha(R/p)==h,p
 r.update(status='passed',full_type_count=len(x['endpoints']),project_dependency_nodes=len(x['project_dependency_graph']),finished_at_utc=now(),expanded_types_sha256=sha(O/'expanded-types.json'));save()
except Exception as e:r.update(status='failed',error=str(e));save();raise
print(json.dumps({'status':r['status'],'full_types':r['full_type_count']}))

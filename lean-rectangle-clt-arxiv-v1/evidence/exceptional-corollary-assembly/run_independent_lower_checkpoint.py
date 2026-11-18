import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent;O=P/'independent-lower-checkpoint-1';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
L=json.loads((R/'correspondence/exceptional-corollary-assembly-passages.json').read_text());targets=[];sources={}
for n in ['checkpoint-2','checkpoint-time-integral-1']:
 d=json.loads((P/n/'run.json').read_text());assert d['status']=='passed';targets+=d['targets'];sources.update(d['final_source_identity'])
targets=list(dict.fromkeys(targets+['RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.'+n for n in ['mk','cubic','pair']]))
s=(R/'evidence/early-correspondence/checkpoint-1/TypesAndAudit.lean').read_text();s=re.sub(r'^import RectangleCLTArxivV1.*\n','',s,flags=re.M);s='import RectangleCLTArxivV1.ExceptionalMain\nimport RectangleCLTArxivV1.ExceptionalTimeIntegral\n'+s;s=re.sub(r'let targets := #\[.*?\]\n  let mut queue','let targets := #[\n'+',\n'.join('    ``'+n for n in targets)+']\n  let mut queue',s,flags=re.S)
s=s.replace('  let mut queue := targets.toList','  let env ← getEnv\n  let (_, axiomState) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}\n  let forbidden := axiomState.axioms.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n\n  unless forbidden.isEmpty do throwError "Unexpected axiom in endpoint union: {forbidden}"\n  let mut queue := targets.toList');s=s.replace('      let axioms ← Lean.collectAxioms target\n      let forbidden := axioms.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n\n      unless forbidden.isEmpty do\n        throwError "Unexpected axioms in {target}: {forbidden}"\n','');s=s.replace('Fresh early passage correspondence: C1 bounded/Gaussian, Corollary1 normalization, Lemma2 actual endpoint smoothing; no q0 derivative correspondence claim','Independent conditional Corollary5 actual split/restoration/time/optimization review; precise full cubic/angle matrix supplier remains explicit, raw Cor5 open')
(O/'TypesAndAudit.lean').write_text(s);(O/'targets.json').write_text(json.dumps(targets,indent=2)+'\n')
for p,h in sources.items():assert sha(R/p)==h,p
r={'status':'running','scope':'Independent selected build/all9 source forces, strict standard-three axiom union over all36 endpoints plus supplier constructor/fields, full types and kernel project dependencies; conditional Corollary5 only.','release_wide_certification':False,'initial_checkout_clean':False,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'source_identity':sources,'frozen_ledger_sha256':sha(R/'correspondence/exceptional-corollary-assembly-passages.json'),'strict_targets':targets,'axiom_strategy':'Complete shared kernel axiom-union over all targets; an allowed union implies every endpoint is allowed.','started_at_utc':now(),'commands':[]}
def save():(O/'run.json').write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
def run(label,argv):
 x={'label':label,'argv':argv,'started_at_utc':now(),'log':str((O/(label+'.log')).relative_to(R))};r['commands'].append(x);save()
 with (R/x['log']).open('wb') as f:p=subprocess.run(argv,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
 x.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(R/x['log']));save()
 if p.returncode:raise RuntimeError(label+' failed')
try:
 save();run('build',['lake','build','RectangleCLTArxivV1.ExceptionalMain','RectangleCLTArxivV1.ExceptionalTimeIntegral'])
 for p in L['source_identity']:run('force-'+Path(p).stem,['lake','env','lean',p])
 run('types-and-strict-audit',['lake','env','lean',str((O/'TypesAndAudit.lean').relative_to(R))]);d=json.loads(next(x for x in (O/'types-and-strict-audit.log').read_text().splitlines() if x.startswith('{')));(O/'expanded-types.json').write_text(json.dumps(d,indent=2)+'\n')
 for p,h in sources.items():assert sha(R/p)==h,p
 assert sha(R/'correspondence/exceptional-corollary-assembly-passages.json')==r['frozen_ledger_sha256']
 r.update(status='passed',full_type_count=len(d['endpoints']),project_dependency_nodes=len(d['project_dependency_graph']),expanded_types_sha256=sha(O/'expanded-types.json'),finished_at_utc=now());save()
except Exception as e:r.update(status='failed',error=str(e),finished_at_utc=now());save();raise
print(json.dumps({k:r[k] for k in ['status','full_type_count','project_dependency_nodes']}))

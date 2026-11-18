from pathlib import Path
import json,re,hashlib,datetime,os,subprocess
R=Path(__file__).resolve().parents[2];O=Path(__file__).resolve().parent/'projected-matrix-route-checkpoint-1';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
targets=['RectangleCLT.Companion.SplitV4.'+n for n in ['projected_logistic_matrix_bound', 'logisticPrivateBase', 'logisticPrivateBase_dot', 'logisticPrivateBase_projected_law', 'logisticPrivateBase_concentrated', 'logisticPrivateBase_weight_tendsto', 'logisticPrivateBase_nuclear_sum_tendsto', 'RectangleBaseConcentration.active_coordinate_concentration', 'RectangleBaseConcentration.active_transitionMassBound', 'sum_selector_nuclear_eq_active']]
s=(R/'evidence/early-correspondence/checkpoint-1/TypesAndAudit.lean').read_text();s=re.sub(r'^import RectangleCLTArxivV1.*\n','',s,flags=re.M);s='import RectangleCLTCompanion.SplitV4.LogisticSelectorMatrixBound\n'+s;s=re.sub(r'let targets := #\[.*?\]\n  let mut queue','let targets := #[\n'+',\n'.join('    ``'+n for n in targets)+']\n  let mut queue',s,flags=re.S);(O/'TypesAndAudit.lean').write_text(s)
sources={p:sha(R/p) for p in ['../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticProjectedBound.lean', '../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticProjectedPadding.lean', '../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticActiveConcentration.lean', '../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticActiveFaces.lean', '../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticSelectorMatrixBound.lean']}
r={'status':'running','scope':'Actual projected-base selector route: active face pullback, genuinely constructed private padding, and actual score limit; complements the separately checked physical-base padding route. No final CLT supplier.','release_wide_certification':False,'source_identity':sources,'targets':targets,'commands':[]}
def save():(O/'run.json').write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
try:
 save()
 for label,argv in [('build',['lake','build','RectangleCLTCompanion.SplitV4.LogisticSelectorMatrixBound']),('force',['lake','env','lean','../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticProjectedBound.lean']),('types-and-strict-audit',['lake','env','lean',str((O/'TypesAndAudit.lean').relative_to(R))])]:
  x={'label':label,'argv':argv,'started_at_utc':now(),'log':str((O/(label+'.log')).relative_to(R))};r['commands'].append(x);save()
  with (R/x['log']).open('wb') as f:p=subprocess.run(argv,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  x.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(R/x['log']));save();assert p.returncode==0,label
 x=json.loads(next(l for l in (O/'types-and-strict-audit.log').read_text().splitlines() if l.startswith('{')));(O/'expanded-types.json').write_text(json.dumps(x,indent=2)+'\n')
 for p,h in sources.items():assert sha(R/p)==h,p
 r.update(status='passed',full_type_count=len(x['endpoints']),project_dependency_nodes=len(x['project_dependency_graph']),finished_at_utc=now(),expanded_types_sha256=sha(O/'expanded-types.json'));save()
except Exception as e:r.update(status='failed',error=str(e));save();raise
print(json.dumps({'status':r['status'],'full_types':r['full_type_count']}))

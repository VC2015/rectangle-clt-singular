import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; OUT=Path(__file__).resolve().parent/'support-checkpoint-1';OUT.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
A='RectangleCLT.Companion.SplitV4.';P=A+'Printed.';N='RectangleCLTArxivV1.'
targets=[A+'cube_average_one_column_contraction',A+'intrinsicCubeMean_square_le',A+'smoothGaussianFaceHessian_trace',A+'gaussianAffineMaximum_level_zero',A+'gaussianAffineMaximum_noAtoms',P+'clockLogVector',P+'clockLogMaximum',P+'randomThresholdRadius','RectangleCLT.FaceSmoother.integral_F_eq_randomRectangle_average',N+'normalizedObservationArray',N+'intrinsicObservationRate','RectangleCLT.Companion.normalizedObservationSum',N+'intrinsicBoundaryCoefficient']
s= (OUT.parent/'checkpoint-1/TypesAndAudit.lean').read_text();s=re.sub(r'let targets := #\[.*?\]\n  let mut queue', 'let targets := #[\n'+',\n'.join('    ``'+n for n in targets)+']\n  let mut queue',s,flags=re.S)
s=s.replace('Fresh early passage correspondence: C1 bounded/Gaussian, Corollary1 normalization, Lemma2 actual endpoint smoothing; no q0 derivative correspondence claim','Fresh supporting exact definitions/formulas for early correspondence; no q0 derivative correspondence claim')
(OUT/'TypesAndAudit.lean').write_text(s)
sources=json.loads((OUT.parent/'checkpoint-1/run.json').read_text())['source_sha256'];sources.update({p:sha(ROOT/p) for p in ['../lean-rectangle-clt-local/RectangleCLT/ExponentialMixture.lean','../lean-rectangle-clt-singular/RectangleCLTCompanion/SubexponentialStatement.lean','RectangleCLTArxivV1/IntrinsicInputs.lean']})
r={'scope':'Supplementary exact full types, definition bodies via project graph, and strict3 axiom audit for actual clock/rate definitions and literal Hessian/contraction/noatom formulas. Selected scope only.','status':'running','source_sha256':sources,'strict_targets':targets,'started_at_utc':now(),'command':['lake','env','lean',str((OUT/'TypesAndAudit.lean').relative_to(ROOT))]};(OUT/'run.json').write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
with (OUT/'types-and-audit.log').open('wb') as f:p=subprocess.run(r['command'],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
r['exit_code']=p.returncode;r['log_sha256']=sha(OUT/'types-and-audit.log')
if p.returncode==0:
 x=json.loads(next(l for l in (OUT/'types-and-audit.log').read_text().splitlines() if l.startswith('{')));(OUT/'expanded-types.json').write_text(json.dumps(x,indent=2)+'\n');r.update(full_type_count=len(x['endpoints']),dependency_nodes=len(x['project_dependency_graph']),expanded_types_sha256=sha(OUT/'expanded-types.json'))
 for f,h in sources.items():assert sha(ROOT/f)==h,f
r.update(status='passed' if p.returncode==0 else 'failed',finished_at_utc=now());(OUT/'run.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['status','exit_code','full_type_count','dependency_nodes'] if k in r}))

import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
P=Path(__file__).resolve().parents[3]
D=Path(__file__).resolve().parent
mods=['SupplementalGArrayDecomposition']
files=[P/'RectangleCLTArxivV1'/f'{m}.lean' for m in mods]
files += [P/'RectangleCLTArxivV1/SupplementalGRectangularTensor.lean',P/'RectangleCLTArxivV1/SupplementalGRectangularDecomposition.lean',P/'RectangleCLTArxivV1/SupplementalGScoreRestoration.lean',P/'RectangleCLTArxivV1/SupplementalGPairMoments.lean',P/'RectangleCLTArxivV1/SupplementalGPairDerivative.lean',P/'RectangleCLTArxivV1/SupplementalGFaceMass.lean',P/'RectangleCLTArxivV1/SupplementalGGeometry.lean',P/'RectangleCLTArxivV1/CapWeightMass.lean',P/'RectangleCLTArxivV1/CapSmallBox.lean',P/'RectangleCLTArxivV1/BoundedCharacteristicFunction.lean',P/'lakefile.toml',P/'lake-manifest.json',P/'lean-toolchain',D/'Audit.lean',D/'Types.lean',Path(__file__)]
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
identity=lambda:{str(p.relative_to(P)):sha(p) for p in files}
report={'scope':'Exact actual fourth-restoration array decomposition into signed single H3 and ordered-pair H2 expectations. Actual score moments justify all Fubini and finite sums. Gaussian-base-observation-copy order. Passage correspondence review remains separate.','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'source_identity':identity(),'commands':[],'status':'running'}
def save(): (D/'run.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,cmd):
 log=D/(label+'.log');row={'label':label,'argv':cmd,'cwd':str(P),'started_at_utc':now(),'log':str(log.relative_to(P))};report['commands'].append(row);save()
 with log.open('wb') as s: r=subprocess.run(cmd,cwd=P,stdout=s,stderr=subprocess.STDOUT,env=os.environ)
 row.update(exit_code=r.returncode,finished_at_utc=now(),log_sha256=sha(log));save()
 if r.returncode: raise RuntimeError(f'{label} failed')
 print(label,'PASS',flush=True)
try:
 run('01-build',['lake','build','RectangleCLTArxivV1.SupplementalGArrayDecomposition'])
 for i,m in enumerate(mods,2):run(f'{i:02d}-force-{m}',['lake','env','lean',f'RectangleCLTArxivV1/{m}.lean','-o',f'.lake/build/lib/lean/RectangleCLTArxivV1/{m}.olean'])
 run('03-audit',['lake','env','lean',str((D/'Audit.lean').relative_to(P))])
 audit=json.loads((D/'03-audit.log').read_text());assert audit['all_axioms_allowed'];report['public_declarations_audited']=len(audit['targets'])
 run('04-types-dependencies',['lake','env','lean',str((D/'Types.lean').relative_to(P))])
 ty=json.loads((D/'04-types-dependencies.log').read_text());report['expanded_types']=len(ty['endpoints']);report['project_dependency_nodes']=len(ty['project_dependency_graph'])
 assert identity()==report['source_identity'],'Owned sources changed during checkpoint'
 report.update(status='passed',finished_at_utc=now(),final_source_identity=identity());save();print('Checkpoint PASS',str(D/'run.json'))
except Exception as e:
 report.update(status='failed',error=str(e),finished_at_utc=now());save();raise

import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
P=Path(__file__).resolve().parents[3]
D=Path(__file__).resolve().parent
mods=['SupplementalHTripleTransportSections', 'SupplementalHTripleTransportCoordinates', 'SupplementalHTripleTransportDensity', 'SupplementalHTripleTransportFrame', 'SupplementalHTripleTransportCone', 'SupplementalHTripleTransportGeometry', 'SupplementalHTripleTransportIncidence', 'SupplementalHTripleTransportThreeFace']
files=[P/'RectangleCLTArxivV1'/f'{m}.lean' for m in mods]
files += [P/x for x in ['RectangleCLTArxivV1/SupplementalHTripleFiber.lean', 'RectangleCLTArxivV1/SupplementalHFrameSections.lean', 'RectangleCLTArxivV1/SupplementalHSphericalPolar.lean', 'RectangleCLTArxivV1/SupplementalHRadius.lean', 'RectangleCLTArxivV1/SupplementalHFourthTransportGeometry.lean', 'RectangleCLTArxivV1/SupplementalHFourthTransportThreeFace.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']]+[D/'Audit.lean',D/'Types.lean',Path(__file__)]
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
identity=lambda:{str(p.relative_to(P)):sha(p) for p in files}
report={'scope':'Actual independent three-normal Gaussian section law, genuine tuple/Euclidean volume and Gaussian equivalences, exact normalized density, unbounded integrable normal-fiber domination, actual isometric frame/projection, true spherical cone-vector coefficient to ambient R4 event, actual positive normal cone/nearest-base outward geometry, factor6 for arbitrary finite injectively indexed triple subfamilies, and actual three-face-radius normal-point/moment discharge. Does not claim actual J_e incidence/Green assembly or full H1.','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'source_identity':identity(),'commands':[],'status':'running'}
def save(): (D/'run.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,cmd):
 log=D/(label+'.log');row={'label':label,'argv':cmd,'cwd':str(P),'started_at_utc':now(),'log':str(log.relative_to(P))};report['commands'].append(row);save()
 with log.open('wb') as s: r=subprocess.run(cmd,cwd=P,stdout=s,stderr=subprocess.STDOUT,env=os.environ)
 row.update(exit_code=r.returncode,finished_at_utc=now(),log_sha256=sha(log));save()
 if r.returncode: raise RuntimeError(f'{label} failed')
 print(label,'PASS',flush=True)
try:
 run('01-build',['lake','build']+['RectangleCLTArxivV1.'+m for m in mods])
 for i,m in enumerate(mods,2):run(f'{i:02d}-force-{m}',['lake','env','lean',f'RectangleCLTArxivV1/{m}.lean','-o',f'.lake/build/lib/lean/RectangleCLTArxivV1/{m}.olean'])
 run('10-audit',['lake','env','lean',str((D/'Audit.lean').relative_to(P))])
 audit=json.loads((D/'10-audit.log').read_text());assert audit['all_axioms_allowed'];report['public_declarations_audited']=len(audit['targets'])
 run('11-types-dependencies',['lake','env','lean',str((D/'Types.lean').relative_to(P))])
 ty=json.loads((D/'11-types-dependencies.log').read_text());report['expanded_types']=len(ty['endpoints']);report['project_dependency_nodes']=len(ty['project_dependency_graph'])
 assert identity()==report['source_identity'],'Owned sources changed during checkpoint'
 report.update(status='passed',finished_at_utc=now(),final_source_identity=identity());save();print('Checkpoint PASS',str(D/'run.json'))
except Exception as e:
 report.update(status='failed',error=str(e),finished_at_utc=now());save();raise

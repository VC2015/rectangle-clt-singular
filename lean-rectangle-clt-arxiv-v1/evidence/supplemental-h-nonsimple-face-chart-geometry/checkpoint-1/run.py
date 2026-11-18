#!/usr/bin/env python3
"""Fresh build/source/axiom/type checkpoint for actual three-normal chart geometry.

Run this preserved runner with --root PROJECT --output FRESH_DIRECTORY.
An existing run.json is refused; fixtures are copied from this checkpoint.
This checks actual chart geometry, not a supplied law/mass or final H1 theorem.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--root',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args();P=args.root.resolve();E=args.output.resolve()
E.mkdir(parents=True,exist_ok=True)
receipt=E/'run.json'
if receipt.exists():raise SystemExit('Refusing to overwrite an existing receipt')
fixture_root=Path(__file__).resolve().parent
for name in ['Audit.lean','Types.lean','run.py']:
 source=fixture_root/name;target=E/name
 if source.resolve()!=target.resolve():shutil.copyfile(source,target)
source=Path('RectangleCLTArxivV1/SupplementalHNonsimpleFaceChartGeometry.lean')
expected='de0041c4bfe3c6591fcd90611bd7679eba85d9a35fd83d76ff43f9ff9afbdbf0'
assert sha(P/source)==expected,'Constructed-model source differs from frozen witness'
names=['RectangleCLTArxivV1.'+n for n in re.findall(
 r'^(?:def|theorem|lemma)\s+([A-Za-z0-9_]+)',(P/source).read_text(),re.M)]
assert len(names)==25
upstream=[Path('RectangleCLTArxivV1/'+m+'.lean') for m in ['SupplementalHFrameSections','SupplementalHNormalChartIsometry']]
bound=[source]+upstream+[Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')]
identity={str(f):sha(P/f) for f in bound}
fixture_identity={n:sha(E/n) for n in ['Audit.lean','Types.lean','run.py']}
run={'status':'running','scope':'Actual orthonormal extension with three given normal rays in the last3 coordinates, affine chart onto all three supporting hyperplanes, Euclidean affine isometry and norm/kernel factorization, plus exact physical Gaussian-frame section after rotation equals the chart at the firstn coordinates. No Gaussian law, product-measure/Fubini, surface or mass supplier premise is assumed; canonical mass and original H1 claims are outside this geometry component.','release_wide_certification':False,'started_at_utc':now(),
 'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),
 'initial_checkout_clean':not subprocess.check_output(['git','status','--porcelain'],cwd=P,text=True).strip(),
 'source_identity':identity,'fixture_identity':fixture_identity,'targets':names,'commands':[]}
env=dict(os.environ,PATH='/workspace/lean-toolchain-bin/bin:'+os.environ['PATH'])
def save():receipt.write_text(json.dumps(run,indent=2)+'\n')
def command(label,argv):
 row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str(E/(label+'.log'))}
 run['commands'].append(row);save()
 with Path(row['log']).open('wb') as stream:result=subprocess.run(argv,cwd=P,env=env,stdout=stream,stderr=subprocess.STDOUT)
 row.update(exit_code=result.returncode,finished_at_utc=now(),log_sha256=sha(Path(row['log'])));save()
 if result.returncode:raise RuntimeError(label+' failed')
try:
 command('01-build',['lake','build','RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartGeometry'])
 command('02-force-source',['lake','env','lean',str(source),'-o','.lake/build/lib/lean/RectangleCLTArxivV1/SupplementalHNonsimpleFaceChartGeometry.olean'])
 command('03-strict-audit',['lake','env','lean',str(E/'Audit.lean')])
 audit=json.loads((E/'03-strict-audit.log').read_text())
 assert audit['all_axioms_allowed'] and [x['name'] for x in audit['targets']]==names
 command('04-full-types-dependencies',['lake','env','lean',str(E/'Types.lean')])
 types=json.loads((E/'04-full-types-dependencies.log').read_text())
 endpoints={x['name']:x for x in types['endpoints']}
 graph={x['name']:x['direct_project_dependencies'] for x in types['project_dependency_graph']}
 assert len(endpoints)==25 and set(endpoints)==set(names)
 assert all(endpoints[n]['expanded_type'].strip() for n in names)
 assert all(n in graph for ds in graph.values() for n in ds)
 def closure(n):
  todo=[n];seen=set()
  while todo:
   x=todo.pop()
   if x in seen:continue
   seen.add(x);todo.extend(graph.get(x,[]))
  return seen
 vertex=closure('RectangleCLTArxivV1.nonsimpleFaceChart_rotated_section')
 for target in ['nonsimpleFaceChartBasis_exists','nonsimpleFaceChartBasis_normal','nonsimpleFaceChart_normalSum_eq_rotation','nonsimpleFaceChart_rotated_inner','gaussianFrameSectionPoint','gaussianFrameProjection']:
  assert 'RectangleCLTArxivV1.'+target in vertex,target
 affine=closure('RectangleCLTArxivV1.nonsimpleFaceChartAffineIsometry_apply')
 assert 'RectangleCLTArxivV1.nonsimpleFaceTangentAppend' in affine
 assert 'RectangleCLTArxivV1.nonsimpleFaceEuclideanAppend_normSq' in affine
 assert identity=={str(f):sha(P/f) for f in bound},'Source changed during checkpoint'
 assert fixture_identity=={n:sha(E/n) for n in fixture_identity},'Fixture changed during checkpoint'
 assertions={'status':'passed','orthonormal_extension_and_actual_rotated_section_routes':True,'actual_Euclidean_affine_isometry_and_norm_routes':True,'normal_ray_positions_are_fixed_last_three':True,'no_Gaussian_law_Fubini_surface_or_mass_supplier_premise':True,'no_canonical_mass_or_final_H1_claim':True,'rotated_section_project_nodes':len(vertex),'affine_chart_project_nodes':len(affine)}
 (E/'model-assertions.json').write_text(json.dumps(assertions,indent=2)+'\n')
 run.update(status='passed',public_declarations_audited=25,expanded_types=25,project_dependency_nodes=len(graph),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as error:
 run.update(status='failed',error=str(error),finished_at_utc=now());raise
finally:save()
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

#!/usr/bin/env python3
"""Fresh build/source/axiom/type checkpoint for actual four-edge square balance.

Run this preserved runner with --root PROJECT --output FRESH_DIRECTORY.
An existing run.json is refused; fixtures are copied from this checkpoint.
This checks an actual nonsimple four-edge balance instantiation, not a final H.1 Green claim.
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
source=Path('RectangleCLTArxivV1/SupplementalHNonsimpleSquareBalance.lean')
expected='2b76ca5c8256ff9cf5df40c716c35db1ea1c476cdd6a7a97154ccb43736b1b15'
assert sha(P/source)==expected,'Constructed-model source differs from frozen witness'
names=['RectangleCLTArxivV1.'+n for n in re.findall(
 r'^(?:def|theorem|lemma)\s+([A-Za-z0-9_]+)',(P/source).read_text(),re.M)]
assert len(names)==26
upstream=[Path('RectangleCLTArxivV1/'+m+'.lean') for m in ['SupplementalHNonsimpleExample','SupplementalHSphericalPolygonCoverage','SupplementalHSphericalPolygonBalance','SupplementalHSphericalPolygonDual','SupplementalHSphericalPolygonPolar']]
bound=[source]+upstream+[Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')]
identity={str(f):sha(P/f) for f in bound}
fixture_identity={n:sha(E/n) for n in ['Audit.lean','Types.lean','run.py']}
run={'status':'running','scope':'Actual four-edge spherical balance on the fixed nonsimple square normal cone. Every unit ray, conormal, incidence, strict sign, span, strict polar point and finite nonzero supporting-pair ray coverage condition is proved internally. Final identity and area-norm bound have no parameters or supplier hypotheses. This component does not claim the final nonsimple ridge Green identity or the full original-polyhedron H1 theorem.','release_wide_certification':False,'started_at_utc':now(),
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
 command('01-build',['lake','build','RectangleCLTArxivV1.SupplementalHNonsimpleSquareBalance'])
 command('02-force-source',['lake','env','lean',str(source),'-o','.lake/build/lib/lean/RectangleCLTArxivV1/SupplementalHNonsimpleSquareBalance.olean'])
 command('03-strict-audit',['lake','env','lean',str(E/'Audit.lean')])
 audit=json.loads((E/'03-strict-audit.log').read_text())
 assert audit['all_axioms_allowed'] and [x['name'] for x in audit['targets']]==names
 command('04-full-types-dependencies',['lake','env','lean',str(E/'Types.lean')])
 types=json.loads((E/'04-full-types-dependencies.log').read_text())
 endpoints={x['name']:x for x in types['endpoints']}
 graph={x['name']:x['direct_project_dependencies'] for x in types['project_dependency_graph']}
 assert len(endpoints)==26 and set(endpoints)==set(names)
 assert all(endpoints[n]['expanded_type'].strip() for n in names)
 assert all(n in graph for ds in graph.values() for n in ds)
 def closure(n):
  todo=[n];seen=set()
  while todo:
   x=todo.pop()
   if x in seen:continue
   seen.add(x);todo.extend(graph.get(x,[]))
  return seen
 vertex=closure('RectangleCLTArxivV1.nonsimpleSquare_four_edge_spherical_balance')
 for target in ['nonsimpleSquare_nonzero_polar_incident_coverage','nonsimpleSquare_polar_zero_pair_is_edge','nonsimpleSquare_polar_edge_multiple','sphericalPolygon_nonzero_incident_balance','sphericalPolygonGeneratedCone_mem_iff_supporting_pairs','sphericalPolygon_polar_linear_nonneg_of_two_zero','sphericalPolygon_generated_balance','sphericalPolygonGeneratedCone_zero_face_eq_wedge','sphericalPolygonFacetChart_angular_area']:
  assert 'RectangleCLTArxivV1.'+target in vertex,target
 assert identity=={str(f):sha(P/f) for f in bound},'Source changed during checkpoint'
 assert fixture_identity=={n:sha(E/n) for n in fixture_identity},'Fixture changed during checkpoint'
 assertions={'status':'passed','final_concrete_identity_and_norm_types_have_no_parameters_or_supplier_hypotheses':True,'kernel_type_forall_check_performed_in_Types_lean':True,'actual_four_edge_incidence_and_nonzero_polar_ray_coverage_routes':True,'generic_support_coefficient_and_angular_chart_routes_reached':True,'no_final_printed_H1_Green_claim':True,'balance_project_nodes':len(vertex)}
 (E/'model-assertions.json').write_text(json.dumps(assertions,indent=2)+'\n')
 run.update(status='passed',public_declarations_audited=26,expanded_types=26,project_dependency_nodes=len(graph),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as error:
 run.update(status='failed',error=str(error),finished_at_utc=now());raise
finally:save()
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

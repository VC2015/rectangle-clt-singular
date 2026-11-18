#!/usr/bin/env python3
"""Fresh build/source/axiom/type checkpoint for the constructed square cone.

Run this preserved runner with --root PROJECT --output FRESH_DIRECTORY.
An existing run.json is refused; fixtures are copied from this checkpoint.
This checks a constructed verification witness, not a printed H.1 claim.
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
source=Path('RectangleCLTArxivV1/SupplementalHNonsimpleExample.lean')
expected='82c68e4a0d4a36f75b702cb131d98187882b0632a44ab97cc9c32ef88a5454ff'
assert sha(P/source)==expected,'Constructed-model source differs from frozen witness'
names=['RectangleCLTArxivV1.'+n for n in re.findall(
 r'^(?:def|theorem|lemma)\s+([A-Za-z0-9_]+)',(P/source).read_text(),re.M)]
assert len(names)==29
upstream=[Path('RectangleCLTArxivV1/SupplementalHNonsimpleFaceGeometry.lean'),
 Path('RectangleCLTArxivV1/SupplementalHSphericalBalance.lean')]
bound=[source]+upstream+[Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')]
identity={str(f):sha(P/f) for f in bound}
fixture_identity={n:sha(E/n) for n in ['Audit.lean','Types.lean','run.py']}
run={'status':'running','scope':'Constructed actual nonsimple square-cone verification witness: four unit genuine facets, exact primal inequalities, explicit strict interior/deletion witnesses, actual normal rank three and a native four-active-facet NonsimpleFaceIndex with exact stratum {0}. No final printed H1 assertion or literal nonsimple Green identity is certified.','release_wide_certification':False,'started_at_utc':now(),
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
 command('01-build',['lake','build','RectangleCLTArxivV1.SupplementalHNonsimpleExample'])
 command('02-force-source',['lake','env','lean',str(source),'-o','.lake/build/lib/lean/RectangleCLTArxivV1/SupplementalHNonsimpleExample.olean'])
 command('03-strict-audit',['lake','env','lean',str(E/'Audit.lean')])
 audit=json.loads((E/'03-strict-audit.log').read_text())
 assert audit['all_axioms_allowed'] and [x['name'] for x in audit['targets']]==names
 command('04-full-types-dependencies',['lake','env','lean',str(E/'Types.lean')])
 types=json.loads((E/'04-full-types-dependencies.log').read_text())
 endpoints={x['name']:x for x in types['endpoints']}
 graph={x['name']:x['direct_project_dependencies'] for x in types['project_dependency_graph']}
 assert len(endpoints)==29 and set(endpoints)==set(names)
 assert all(endpoints[n]['expanded_type'].strip() for n in names)
 assert all(n in graph for ds in graph.values() for n in ds)
 def closure(n):
  todo=[n];seen=set()
  while todo:
   x=todo.pop()
   if x in seen:continue
   seen.add(x);todo.extend(graph.get(x,[]))
  return seen
 vertex=closure('RectangleCLTArxivV1.nonsimpleSquareActualVertex')
 assert 'RectangleCLTArxivV1.nonsimpleSquare_normal_rank_three' in vertex
 assert 'RectangleCLTArxivV1.nonsimpleSquare_origin_exactStratum' in vertex
 assert 'NonsimpleFaceIndex' in endpoints['RectangleCLTArxivV1.nonsimpleSquareActualVertex']['expanded_type']
 assert identity=={str(f):sha(P/f) for f in bound},'Source changed during checkpoint'
 assert fixture_identity=={n:sha(E/n) for n in fixture_identity},'Fixture changed during checkpoint'
 assertions={'status':'passed','actual_vertex_uses_native_face_index':True,'rank_and_exact_stratum_proofs_are_actual_dependencies':True,'four_active_genuine_facets_and_rank_three_checked':True,'actual_model_is_constructed_support_only':True,'no_final_printed_H1_claim':True,'vertex_project_nodes':len(vertex)}
 (E/'model-assertions.json').write_text(json.dumps(assertions,indent=2)+'\n')
 run.update(status='passed',public_declarations_audited=29,expanded_types=29,project_dependency_nodes=len(graph),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as error:
 run.update(status='failed',error=str(error),finished_at_utc=now());raise
finally:save()
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

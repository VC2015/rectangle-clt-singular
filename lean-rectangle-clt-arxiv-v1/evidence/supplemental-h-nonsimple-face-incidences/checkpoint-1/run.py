#!/usr/bin/env python3
"""Independent fresh check of four author-frozen nonsimple geometry leaves.

Use --root PROJECT --output FRESH_DIRECTORY. Existing receipts are refused.
This records generic geometry endpoints, not a final H1/Green promotion.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
P=args.root.resolve();E=args.output.resolve();E.mkdir(parents=True,exist_ok=True)
rp=E/'run.json'
if rp.exists():raise SystemExit('Refusing to overwrite an existing receipt')
for name in ['Audit.lean','Types.lean','run.py']:
 src=Path(__file__).resolve().parent/name
 if src.resolve()!=(E/name).resolve():shutil.copyfile(src,E/name)
modules=['SupplementalHNonsimpleFaceCofaces','SupplementalHNonsimpleFaceConormal','SupplementalHNonsimpleFaceCoverage','SupplementalHNonsimpleFaceTubes']
expected=['2255e7ffa6b77bd6b5f5e9c9bcc60bdabbebfd0ed911052fcf356954aaee949c','2662aae0f57fa2937975838da3a983dde8d50dbfcc0bdb6ba9b7336e32487c2f','82c96ed92817d53229a3c985b8254664880ee6f62c56f082a90d44506923f563','7191adb2279b1eedcdf5f7bde067d3c11b9a915bc1b8aa6792d5df116ba7db0b']
files=[Path('RectangleCLTArxivV1')/(m+'.lean') for m in modules]
assert [sha(P/f) for f in files]==expected,'Author-frozen source identity mismatch'
targets=['RectangleCLTArxivV1.'+n for f in files for n in re.findall(r'^(?:(?:noncomputable|protected)\s+)*(?:def|theorem|lemma|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_\']*)',(P/f).read_text(),re.M)]
assert len(targets)==len(set(targets))==26
upstream=set()
for f in files:
 for m in re.findall(r'(?m)^import (RectangleCLTArxivV1\.[A-Za-z0-9_]+)\s*$',(P/f).read_text()):upstream.add(Path(m.replace('.','/')+'.lean'))
bound=sorted(set(files)|upstream|{Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')})
ident={str(f):sha(P/f) for f in bound};fixtures={f:sha(E/f) for f in ['Audit.lean','Types.lean','run.py']}
r={'status':'running','reviewer':'polygon_interface_review, independent of bounded_intrinsic author','scope':'Author-frozen new Cofaces/Conormal/Coverage/Tubes only: actual original ridge construction, canonical unit conormal and support signs, nonzero supporting-pair coverage by genuine ridge incidences, and generic full-active-set normal tube disjointness/integral domination. Ordinary frames/levels/cone measurability/R4 integrability remain explicit Tube inputs; no final H1/Green certification.','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_checkout_clean':not subprocess.check_output(['git','status','--porcelain'],cwd=P,text=True).strip(),'source_identity':ident,'fixture_identity':fixtures,'targets':targets,'commands':[]}
env=dict(os.environ,PATH='/workspace/lean-toolchain-bin/bin:'+os.environ['PATH'])
def save():rp.write_text(json.dumps(r,indent=2)+'\n')
def cmd(label,argv):
 row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str(E/(label+'.log'))};r['commands'].append(row);save()
 with Path(row['log']).open('wb') as out:p=subprocess.run(argv,cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
 row.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(Path(row['log'])));save()
 if p.returncode:raise RuntimeError(label+' failed')
try:
 cmd('01-build',['lake','build']+['RectangleCLTArxivV1.'+m for m in modules])
 for i,(m,f) in enumerate(zip(modules,files),2):cmd(f'{i:02}-force-'+m,['lake','env','lean',str(f),'-o','.lake/build/lib/lean/RectangleCLTArxivV1/'+m+'.olean'])
 cmd('06-strict-audit',['lake','env','lean',str(E/'Audit.lean')]);ad=json.loads((E/'06-strict-audit.log').read_text());assert ad['all_axioms_allowed'] and [x['name'] for x in ad['targets']]==targets
 cmd('07-full-types-dependencies',['lake','env','lean',str(E/'Types.lean')]);td=json.loads((E/'07-full-types-dependencies.log').read_text());ends={x['name']:x for x in td['endpoints']};graph={x['name']:x['direct_project_dependencies'] for x in td['project_dependency_graph']}
 assert len(ends)==26 and set(ends)==set(targets) and all(ends[n]['expanded_type'].strip() for n in targets)
 assert all(n in graph for ds in graph.values() for n in ds)
 def closure(start):
  todo=[start];seen=set()
  while todo:
   n=todo.pop()
   if n in seen:continue
   seen.add(n);todo.extend(graph.get(n,[]))
  return seen
 cover=closure('RectangleCLTArxivV1.nonsimple_nonzero_polar_covered_by_actual_incidence')
 for n in ['nonsimple_supporting_pair_has_actual_ridge','nonsimple_supporting_pair_has_actual_stratum','nonsimple_exactStratum_move_to_active_subset','nonsimpleIncidentConormal_unit','sphericalPolygon_conormal_nonneg_smul_of_three']:
  assert 'RectangleCLTArxivV1.'+n in cover,n
 tube=closure('RectangleCLTArxivV1.nonsimpleFaceNormalEvent_integral_sum_le')
 for n in ['nonsimpleFaceNormalEvent_indicator_sum_le','nonsimpleFaceNormalEvent_disjoint','tripleConeEvent_mem_outerLayer','tripleConeEvent_mem_adaptiveOutwardTube']:
  assert 'RectangleCLTArxivV1.'+n in tube,n
 assert ident=={str(f):sha(P/f) for f in bound},'Frozen source/upstream changed during check'
 assert fixtures=={f:sha(E/f) for f in fixtures},'Fixture changed during check'
 (E/'actual-route-assertions.json').write_text(json.dumps({'status':'passed','actual_coface_movement_and_native_conormal_coverage_routes':True,'full_active_set_tube_disjointness_and_layer_route':True,'coverage_project_nodes':len(cover),'tube_project_nodes':len(tube),'generic_tube_frames_levels_measurability_and_R4_inputs_remain_explicit':True,'no_final_H1_or_Green_promotion':True},indent=2)+'\n')
 r.update(status='passed',public_declarations_audited=26,expanded_types=26,project_dependency_nodes=len(graph),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as ex:r.update(status='failed',error=str(ex),finished_at_utc=now());raise
finally:save()
print(json.dumps({k:r[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

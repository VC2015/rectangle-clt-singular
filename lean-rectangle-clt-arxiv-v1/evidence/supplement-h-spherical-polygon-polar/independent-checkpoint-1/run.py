#!/usr/bin/env python3
"""Independent fresh21 polar/conormal/coverage and rank-one kernel check.

Use --root PROJECT --output FRESH_DIRECTORY; existing receipts are refused.
The authored Chart source is imported prior support, not claimed as an
independent human source review. Geometric incident-ray premises remain.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();P=a.root.resolve();E=a.output.resolve();E.mkdir(parents=True,exist_ok=True);rp=E/'run.json'
if rp.exists():raise SystemExit('Refusing an existing receipt')
for n in ['Audit.lean','Types.lean','run.py']:
 p=Path(__file__).resolve().parent/n
 if p.resolve()!=(E/n).resolve():shutil.copyfile(p,E/n)
mods=['SupplementalHSphericalPolygonPolar','SupplementalHSphericalPolygonDual','SupplementalHSphericalPolygonConormal','SupplementalHSphericalPolygonIncidence','SupplementalHSphericalPolygonCoverage','SupplementalHSphericalPolygonRankOne']
expected=['b0039e005be2ef9b33c262166e1a47c68176d535c1c32fba3ee8ddd1feff244c','11ea2c657191d3c1ab60276eaad917461e1a8d9e625270ea892fa1b8d892f78a','10a72818211b94d31babc7ddaaed724c2bd7654b4d7655b02bba79c3bc20643d','74fad4f6549ed9c44dd70775ebdaee671978315a3cc13a0169485ef8d1c1c995','856ed314a21c03ff431f57a37572fc2a515fb4ccd084f70693cff2227054f595','bf8b63128da45d0d3ce98001436a28a6ad76fce34b808503f9966c56a7e0d3a6']
files=[Path('RectangleCLTArxivV1')/(m+'.lean') for m in mods];assert [sha(P/f) for f in files]==expected
targets=['RectangleCLTArxivV1.'+n for f in files for n in re.findall(r'^(?:def|theorem|lemma)\s+([A-Za-z0-9_]+)',(P/f).read_text(),re.M)];assert len(targets)==len(set(targets))==21
upstream=set()
for f in files:
 for m in re.findall(r'(?m)^import (RectangleCLTArxivV1\.[A-Za-z0-9_]+)\s*$',(P/f).read_text()):upstream.add(Path(m.replace('.','/')+'.lean'))
protected=[Path('correspondence/supplemental-h-spherical-polygon-polar-passages.json'),Path('evidence/supplement-h-spherical-polygon-polar/source-freeze.json'),Path('evidence/supplement-h-spherical-polygon-polar/checkpoint-1/run.json'),Path('evidence/supplement-h-spherical-polygon-coverage/checkpoint-1/run.json'),Path('evidence/supplement-h-spherical-polygon-rank-one/checkpoint-1/run.json')]
assert sha(P/protected[0])=='bdd79145bd646989656075dabcaffd9ed0782d1b72211460875c35427e99b209'
bound=sorted(set(files)|upstream|{Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')});identity={str(f):sha(P/f) for f in bound};protected_id={str(f):sha(P/f) for f in protected};fixture_id={n:sha(E/n) for n in ['Audit.lean','Types.lean','run.py']}
r={'status':'running','reviewer':'polygon_interface_review, independent of source author g3_resume','scope':'Independent source/kernel review of Polar/Dual/Conormal/Incidence/Coverage17 exports plus RankOne4 source-bound addendum. Actual finite polar line-cut completeness, signed bipolarity, conormal positivity/proportionality and rank-one residual geometry are proved. Geometric incident-ray coverage remains explicit; no original-polyhedron H1/Green promotion. Authored Chart9 is imported prior support and is explicitly excluded from independent human source-review claims.','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_checkout_clean':not subprocess.check_output(['git','status','--porcelain'],cwd=P,text=True).strip(),'source_identity':identity,'protected_packet_identity':protected_id,'fixture_identity':fixture_id,'targets':targets,'commands':[]}
env=dict(os.environ,PATH='/workspace/lean-toolchain-bin/bin:'+os.environ['PATH'])
def save():rp.write_text(json.dumps(r,indent=2)+'\n')
def cmd(label,argv):
 row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str(E/(label+'.log'))};r['commands'].append(row);save()
 with Path(row['log']).open('wb') as out:q=subprocess.run(argv,cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
 row.update(exit_code=q.returncode,finished_at_utc=now(),log_sha256=sha(Path(row['log'])));save()
 if q.returncode:raise RuntimeError(label+' failed')
try:
 cmd('01-build',['lake','build']+['RectangleCLTArxivV1.'+m for m in mods])
 for i,(m,f) in enumerate(zip(mods,files),2):cmd(f'{i:02}-force-'+m,['lake','env','lean',str(f),'-o','.lake/build/lib/lean/RectangleCLTArxivV1/'+m+'.olean'])
 cmd('08-strict-audit',['lake','env','lean',str(E/'Audit.lean')]);audit=json.loads((E/'08-strict-audit.log').read_text());assert audit['all_axioms_allowed'] and [x['name'] for x in audit['targets']]==targets
 cmd('09-full-types-dependencies',['lake','env','lean',str(E/'Types.lean')]);t=json.loads((E/'09-full-types-dependencies.log').read_text());ends={x['name']:x for x in t['endpoints']};graph={x['name']:x['direct_project_dependencies'] for x in t['project_dependency_graph']};assert len(ends)==21 and set(ends)==set(targets) and all(ends[n]['expanded_type'].strip() for n in targets);assert all(n in graph for ds in graph.values() for n in ds)
 def closure(s):
  todo=[s];seen=set()
  while todo:
   n=todo.pop()
   if n in seen:continue
   seen.add(n);todo.extend(graph.get(n,[]))
  return seen
 cl=closure('RectangleCLTArxivV1.sphericalPolygon_nonzero_incident_balance')
 for n in ['sphericalPolygonGeneratedCone_mem_iff_nonzero_incident_halfspaces','sphericalPolygonGeneratedCone_mem_iff_supporting_pairs','sphericalPolygon_polar_linear_nonneg_of_two_zero','sphericalPolygon_polar_linear_nonneg_of_one_zero','sphericalPolygon_exists_orthogonal_pair','sphericalPolygonGeneratedCone_mem_iff_nonneg_polar','nonsimple_polar_inner_line_split','sphericalPolygon_generated_balance']:
  assert 'RectangleCLTArxivV1.'+n in cl,n
 rank=closure('RectangleCLTArxivV1.sphericalPolygon_orthogonal_range_finrank_le_one_of_three');assert 'RectangleCLTArxivV1.sphericalPolygon_vector_eq_coordinate_normal' in rank
 assert identity=={str(f):sha(P/f) for f in bound}
 assert protected_id=={str(f):sha(P/f) for f in protected}
 assert fixture_id=={n:sha(E/n) for n in fixture_id}
 (E/'actual-route-assertions.json').write_text(json.dumps({'status':'passed','actual_polar_line_cut_and_signed_bipolar_routes':True,'nonzero_coverage_handles_zero_direction_internally':True,'signed_balance_proved_before_norm_bound':True,'rank_one_actual_coordinate_normal_route':True,'incident_ray_coverage_remains_explicit':True,'authored_Chart_source_excluded_from_independent_human_review':True,'balance_project_nodes':len(cl),'rank_one_project_nodes':len(rank)},indent=2)+'\n')
 r.update(status='passed',public_declarations_audited=21,expanded_types=21,project_dependency_nodes=len(graph),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as ex:r.update(status='failed',error=str(ex),finished_at_utc=now());raise
finally:save()
print(json.dumps({k:r[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

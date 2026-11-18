from pathlib import Path
import hashlib,json,subprocess,os,re,datetime
P=Path('/workspace/rectangle-clt-singular/lean-rectangle-clt-arxiv-v1'); E=P/'evidence/supplemental-h-nonsimple-cone-polar-independent/checkpoint-1'; E.mkdir(parents=True,exist_ok=True)
modules=['SupplementalHNonsimpleFaceCone','SupplementalHNonsimpleFacePolarLine']
files=[Path('RectangleCLTArxivV1')/(m+'.lean') for m in modules]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
targets=[]
for f in files:
 for n in re.findall(r'^(?:@\[[^\n]*?\]\s*)?(?:theorem|def|lemma|structure)\s+([A-Za-z0-9_]+)',(P/f).read_text(),re.M):targets.append('RectangleCLTArxivV1.'+n)
imports=''.join('import RectangleCLTArxivV1.'+m+'\n' for m in modules)
arr='#[\n    '+',\n    '.join('``'+n for n in targets)+']'
audit=imports+'''import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := TARGETS
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
'''.replace('TARGETS',arr)
(E/'Audit.lean').write_text(audit)
types=(P/'evidence/supplement-i/seeded-kernel-checkpoint-1/Types.lean').read_text()
start=types.index('  let targets :=');end=types.index('  let mut queue',start)
types=imports+types[types.index('import Lean.Util.CollectAxioms'):start]+'  let targets := '+arr+'\n'+types[end:]
types=types.replace('Actual seeded theta measurability, scalar-kernel separated/exceptional R4 split and exceptional budget bound','Actual finite generated cone support-face, native chart angular identification and arbitrary-edge polygon balance under explicit geometric halfspace completeness')
(E/'Types.lean').write_text(types)
script=E/'run.py'
if script.resolve()!=Path(__file__).resolve():script.write_text(Path(__file__).read_text())
bound=files+[E.relative_to(P)/'Audit.lean',E.relative_to(P)/'Types.lean',E.relative_to(P)/'run.py',Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')]
ident={str(f):sha(P/f) for f in bound}
run={'initial_checkout_clean':not subprocess.check_output(['git','status','--porcelain'],cwd=P,text=True).strip(),'scope':'Actual finite generated normal-cone support-face coefficient elimination, tangent-chart angular identification and arbitrary-edge spherical polygon balance. Actual generator/facet incidence and halfspace completeness are explicit geometric inputs; no balance, area or angular mass supplier is assumed. This packet does not yet instantiate every nonsimple face of the original polyhedron.','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'source_identity':ident,'commands':[],'status':'running','targets':targets}
receipt=E/'run.json'
env=dict(os.environ,PATH='/workspace/lean-toolchain-bin/bin:'+os.environ['PATH'])
def cmd(label,argv):
 row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str((E/(label+'.log')).relative_to(P))};run['commands'].append(row);receipt.write_text(json.dumps(run,indent=2)+'\n')
 with (P/row['log']).open('w') as out:r=subprocess.run(argv,cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
 row.update(exit_code=r.returncode,finished_at_utc=now(),log_sha256=sha(P/row['log']));receipt.write_text(json.dumps(run,indent=2)+'\n')
 if r.returncode:raise RuntimeError(label)
try:
 cmd('01-build',['lake','build']+['RectangleCLTArxivV1.'+m for m in modules])
 for i,m in enumerate(modules,2):cmd(f'{i:02}-force-{m}',['lake','env','lean',str(Path('RectangleCLTArxivV1')/(m+'.lean')),'-o',f'.lake/build/lib/lean/RectangleCLTArxivV1/{m}.olean'])
 cmd('14-audit',['lake','env','lean',str((E/'Audit.lean').relative_to(P))])
 auditdata=json.loads((E/'14-audit.log').read_text());assert auditdata['all_axioms_allowed'] and len(auditdata['targets'])==len(targets)
 cmd('15-types-dependencies',['lake','env','lean',str((E/'Types.lean').relative_to(P))])
 td=json.loads((E/'15-types-dependencies.log').read_text());assert len(td['endpoints'])==len(targets)
 graph={x['name']:x['direct_project_dependencies'] for x in td['project_dependency_graph']}
 def closure(start):
  pending=[start];seen=set()
  while pending:
   name=pending.pop()
   if name in seen:continue
   seen.add(name);pending.extend(graph.get(name,[]))
  return seen
 endpoints={x['name']:x for x in td['endpoints']}
 assert len(targets)==21
 author_records=[]
 for folder in ['supplemental-h-nonsimple-face-cone','supplemental-h-nonsimple-face-polar-line']:
  ae=P/'evidence'/folder/'checkpoint-1'; ar=json.loads((ae/'run.json').read_text());assert ar['status'].lower() in ['pass','passed']
  for f,h in ar['source_identity'].items():assert sha(P/f)==h
  for row in ar['commands']:
   assert row['exit_code']==0 and sha(P/row['log'])==row['log_sha256']
  at=json.loads((ae/'expanded-types.json').read_text())
  for e in at['endpoints']:
   assert endpoints[e['name']]['expanded_type']==e['expanded_type'],e['name']
   assert set(endpoints[e['name']]['direct_dependencies'])==set(e['direct_dependencies']),e['name']
  author_records.append({'receipt':str((ae/'run.json').relative_to(P)),'sha256':sha(ae/'run.json'),'status':ar['status'],'targets':len(at['endpoints'])})
 cl=closure('RectangleCLTArxivV1.nonsimpleGeneratedCone_mem_iff_polar')
 for n in ['nonsimpleGeneratedCone_isClosed','nonsimpleGeneratedCone_coefficient_bound']:assert 'RectangleCLTArxivV1.'+n in cl,n
 clp=closure('RectangleCLTArxivV1.nonsimple_polar_inner_line_split')
 for n in ['nonsimple_polar_line_split','nonsimple_polar_positive_endpoint','nonsimple_polar_negative_endpoint','nonsimple_polar_line_vector_decomposition']:assert 'RectangleCLTArxivV1.'+n in clp,n
 (E/'actual-route-assertions.json').write_text(json.dumps({'status':'passed','author_records':author_records,'author20_expanded_types_and_direct_dependencies_exact':True,'additional_public_simp_helper_checked':'RectangleCLTArxivV1.mem_nonsimpleGeneratedCone','actual_strict_polar_compactness_and_finite_clipping_routes':True,'declared_geometry_or_H1_target_bound_not_a_supplier':True},indent=2)+'\n')
 assert ident=={str(f):sha(P/f) for f in bound},'Sources changed during checkpoint'
 run.update(status='passed',public_declarations_audited=len(targets),expanded_types=len(td['endpoints']),project_dependency_nodes=len(td['project_dependency_graph']),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as e:run.update(status='failed',failure=str(e),finished_at_utc=now());raise
finally:receipt.write_text(json.dumps(run,indent=2)+'\n')
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

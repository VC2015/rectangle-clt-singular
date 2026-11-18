from pathlib import Path
import hashlib,json,subprocess,os,re,datetime
P=Path('/workspace/rectangle-clt-singular/lean-rectangle-clt-arxiv-v1'); E=P/'evidence/supplement-h-nonsimple-common-mass/independent-g3-checkpoint-1'; E.mkdir(parents=True,exist_ok=True)
modules=['SupplementalHNonsimpleFaceMass','SupplementalHNonsimpleFaceFrame','SupplementalHNonsimpleActualMass','SupplementalHNonsimpleGreenSum']
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
 assert len(targets)==29
 ae=P/'evidence/supplement-h-nonsimple-common-mass/checkpoint-1';ar=json.loads((ae/'run.json').read_text());assert ar['status']=='passed'
 for f,h in ar['source_identity'].items():assert sha(P/f)==h
 for row in ar['commands']:assert row['exit_code']==0 and sha(P/row['log'])==row['log_sha256']
 at=json.loads((ae/'07-full-types.log').read_text())
 for e in at['endpoints']:
  assert endpoints[e['name']]['expanded_type']==e['expanded_type'],e['name']
  assert set(endpoints[e['name']]['direct_dependencies'])==set(e['direct_dependencies']),e['name']
 assert set(endpoints)==set(ar['targets'])
 ledger=P/'correspondence/supplemental-h-nonsimple-common-mass-passages.json'
 freeze=P/'evidence/supplement-h-nonsimple-common-mass/source-freeze.json'
 fz=json.loads(freeze.read_text());assert sha(ledger)==fz['ledger']['sha256']
 for f,h in fz['source_files'].items():assert sha(P/f)==h
 (E/'actual-route-assertions.json').write_text(json.dumps({'status':'passed','author29_expanded_types_and_direct_dependencies_exact':True,'author_receipt_sha256':sha(ae/'run.json'),'frozen_ledger_sha256':sha(ledger),'frozen_source_freeze_sha256':sha(freeze),'actual_complete_face_mass_and_signed_finite_grouping':True,'no_final_H1_or_Green_identity_claim':True},indent=2)+'\n')
 assert ident=={str(f):sha(P/f) for f in bound},'Sources changed during checkpoint'
 run.update(status='passed',public_declarations_audited=len(targets),expanded_types=len(td['endpoints']),project_dependency_nodes=len(td['project_dependency_graph']),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as e:run.update(status='failed',failure=str(e),finished_at_utc=now());raise
finally:receipt.write_text(json.dumps(run,indent=2)+'\n')
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

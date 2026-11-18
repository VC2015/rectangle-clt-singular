from pathlib import Path
import hashlib,json,subprocess,os,re,datetime
P=Path('/workspace/rectangle-clt-singular/lean-rectangle-clt-arxiv-v1'); E=P/'evidence/actual-h-corollaries/checkpoint-1'; E.mkdir(parents=True,exist_ok=True)
modules=['ActualMatrixConstant','ActualMatrixTransport','ActualSeededMatrixBase','ActualPairMatrixTransport','ActualNormalizedMatrices','ActualHFourth','ActualCorollaries','ActualRemainderIntegral']
files=[Path('RectangleCLTArxivV1')/(m+'.lean') for m in modules]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
targets=[]
for f in files:
 for n in re.findall(r'^(?:theorem|def|lemma|structure)\s+([A-Za-z0-9_]+)',(P/f).read_text(),re.M):targets.append('RectangleCLTArxivV1.'+n)
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
types=types.replace('Actual seeded theta measurability, scalar-kernel separated/exceptional R4 split and exceptional budget bound','Actual supplier-free H3 finite expectation and Corollaries4/5 with raw normalized source time-L1/integrated budget')
(E/'Types.lean').write_text(types)
script=E/'run.py'
if script.resolve()!=Path(__file__).resolve():script.write_text(Path(__file__).read_text())
bound=files+[E.relative_to(P)/'Audit.lean',E.relative_to(P)/'Types.lean',E.relative_to(P)/'run.py',Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')]
ident={str(f):sha(P/f) for f in bound}
run={'initial_checkout_clean':not subprocess.check_output(['git','status','--porcelain'],cwd=P,text=True).strip(),'scope':'Actual supplier-free H3 finite fourth-derivative expectation, positive-gap Corollary4, exceptional-budget Corollary5, normalized source time-L1 and integrated R4 budget. Native cubic and full-angle pair matrix propositions, physical support/concentration, every normalized seed scale and one numerical constant are instantiated internally. Final CLT/time-integral endpoints assume only the bounded original array and covariance data, plus cutoff/width conditions. No target matrix/R4/derivative/CLT supplier remains.','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'source_identity':ident,'commands':[],'status':'running','targets':targets}
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
 heads=['theorem_H3_fourth_derivative','corollary4_positive_correlation_gap','corollary5_exceptional_correlation_budget']
 rawTypeChecks={}
 for head in heads+['corollary5_normalized_remainder_integral','corollary5_normalized_remainder_abs_intervalIntegrable']:
  name='RectangleCLTArxivV1.'+head;ty=endpoints[name]['expanded_type']
  forbidden=['MatrixEstimates','matrix_suppliers','GapNormalizedMatrixEstimates','ExceptionalNormalizedMatrixEstimates']
  assert not any(token in ty for token in forbidden),(head,'matrix supplier in final type')
  if head!='theorem_H3_fourth_derivative':assert 'IntrinsicRectangleConcentration' not in ty,(head,'raw concentration supplier')
  rawTypeChecks[head]={'no_matrix_supplier_hypothesis':True,'no_raw_concentration_supplier':head!='theorem_H3_fourth_derivative'}
 actualRoutes={}
 for head in heads:
  ns=closure('RectangleCLTArxivV1.'+head)
  for target in ['proposition_H1_cubic_matrix_shifted','proposition_H2_pair_matrix_shifted']:
   assert 'RectangleCLTArxivV1.'+target in ns,(head,target)
  actualRoutes[head]={'project_nodes':len(ns),'actual_cubic_and_pair_propositions':True}
 ctor=closure('RectangleCLTArxivV1.actual_normalized_matrix_estimates')
 forbiddenCtor=['RectangleCLTArxivV1.hFourth_expectation_bound_of_matrix_suppliers','RectangleCLTArxivV1.hFourth_seeded_remainder_late_bound_of_matrix_suppliers','RectangleCLTArxivV1.positiveGap_CLT_of_matrix_suppliers','RectangleCLTArxivV1.exceptional_CLT_of_matrix_suppliers','RectangleCLT.Companion.SplitV4.normalizedSeededExpectation']
 assert not set(forbiddenCtor)&ctor,sorted(set(forbiddenCtor)&ctor)
 c5=closure('RectangleCLTArxivV1.corollary5_exceptional_correlation_budget')
 assert 'RectangleCLTArxivV1.hFourth_gap_or_parallel' not in c5
 assert 'RectangleCLTArxivV1.hFourth_copy_pair_zero_outside_gap' not in c5
 (E/'actual-route-assertions.json').write_text(json.dumps({'status':'passed','raw_headline_type_checks':rawTypeChecks,'actual_headline_routes':actualRoutes,'normalized_constructor_project_nodes':len(ctor),'normalized_constructor_has_no_downstream_target_bounds':True,'corollary5_has_no_global_gap_route':True},indent=2)+'\n')
 assert ident=={str(f):sha(P/f) for f in bound},'Sources changed during checkpoint'
 run.update(status='passed',public_declarations_audited=len(targets),expanded_types=len(td['endpoints']),project_dependency_nodes=len(td['project_dependency_graph']),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as e:run.update(status='failed',failure=str(e),finished_at_utc=now());raise
finally:receipt.write_text(json.dumps(run,indent=2)+'\n')
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

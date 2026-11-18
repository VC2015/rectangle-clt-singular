from pathlib import Path
import hashlib,json,subprocess,os,re,datetime
P=Path('/workspace/rectangle-clt-singular/lean-rectangle-clt-arxiv-v1'); E=P/'evidence/exceptional-corollary-assembly/checkpoint-1'; E.mkdir(parents=True,exist_ok=True)
modules=['ExceptionalFourthBound','ExceptionalMatrixSuppliers','ExceptionalSeededTensor','ExceptionalSeededModel','ExceptionalSeededRemainder','ExceptionalComparison','ExceptionalSeededComparison','ExceptionalMain']
files=[Path('RectangleCLTArxivV1')/(m+'.lean') for m in modules]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
targets=[]
for f in files:
 for n in re.findall(r'^(?:theorem|def|lemma|structure)\s+([A-Za-z0-9_]+)',(P/f).read_text(),re.M):targets.append('RectangleCLTArxivV1.'+n)
imports=''.join('import RectangleCLTArxivV1.'+m+'\n' for m in modules)
targets += ['RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.'+n for n in ['mk','cubic','pair']]
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
types=types.replace('Actual seeded theta measurability, scalar-kernel separated/exceptional R4 split and exceptional budget bound','Actual separated/exceptional Corollary5 assembly with precise cubic and full-angle matrix suppliers')
(E/'Types.lean').write_text(types)
script=E/'run.py'
if script.resolve()!=Path(__file__).resolve():script.write_text(Path(__file__).read_text())
bound=files+[E.relative_to(P)/'Audit.lean',E.relative_to(P)/'Types.lean',E.relative_to(P)/'run.py',Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')]
ident={str(f):sha(P/f) for f in bound}
run={'initial_checkout_clean':not subprocess.check_output(['git','status','--porcelain'],cwd=P,text=True).strip(),'scope':'Corollary5 separated/exceptional actual original-array assembly, conditional only on genuine cubic and full-angle matrix nuclear sums on the actual half-base. No global correlation-gap, target R4, derivative or CLT estimate is assumed. Source split, actual restricted coefficient restoration, normalized early/late minimum plus exceptional budget, literal time crossing, initialization/smoothing, larger-of-two-width optimization, capped branches, Gaussian intrinsic-coefficient substitution and printed two-thirds powers are proved.','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'source_identity':ident,'commands':[],'status':'running','targets':targets}
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
 names={x['name'] for x in td['project_dependency_graph']}
 required=['exceptional_seeded_separated_eq_cutoff_product','exceptionalFourth_cutoff_expectation_bound_of_matrix_suppliers','cap_seededFourthRemainder_exceptional_split','cap_seeded_exceptional_remainder_bound','exceptional_integral_minimum_add_constant','cap_time_increment_le','exceptionalBudget_rate_of_small_bandwidth_estimate','exceptionalBudgetRate_eq_printed','exceptionalBudgetRate_le_coefficient','exceptionalBudget_trivial_large_envelope','intrinsicBoundaryCoefficient_le_gaussian','hasDerivAt_normalizedSeededExpectation']
 for name in required:assert 'RectangleCLTArxivV1.'+name in names,name
 for name in ['hFourth_copy_pair_zero_outside_gap','hFourth_gap_or_parallel','positiveGap_CLT_of_matrix_suppliers','positiveGap_boundary_CLT_of_matrix_suppliers']:
  assert 'RectangleCLTArxivV1.'+name not in names,name
 graph={x['name']:x['direct_project_dependencies'] for x in td['project_dependency_graph']}
 pending=['RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates'+suffix for suffix in ['', '.mk','.cubic','.pair']]+['RectangleCLTArxivV1.ExceptionalNormalizedMatrixEstimates'];seen=set()
 while pending:
  name=pending.pop()
  if name in seen:continue
  seen.add(name);pending.extend(graph.get(name,[]))
 bad=[n for n in seen if any(token in n for token in ['Remainder','rectangleDistance','normalizedSeededExpectation','cap_time_increment','_CLT_'])]
 assert not bad,bad
 (E/'actual-route-assertions.json').write_text(json.dumps({'status':'passed','required_actual_routes':required,'forbidden_global_gap_routes':['hFourth_copy_pair_zero_outside_gap','hFourth_gap_or_parallel'],'supplier_definition_closure_nodes':len(seen),'supplier_definition_closure':sorted(seen),'supplier_target_bounds_found':bad},indent=2)+'\n')
 assert ident=={str(f):sha(P/f) for f in bound},'Sources changed during checkpoint'
 run.update(status='passed',public_declarations_audited=len(targets),expanded_types=len(td['endpoints']),project_dependency_nodes=len(td['project_dependency_graph']),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as e:run.update(status='failed',failure=str(e),finished_at_utc=now());raise
finally:receipt.write_text(json.dumps(run,indent=2)+'\n')
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

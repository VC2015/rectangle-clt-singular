from pathlib import Path
import hashlib,json,subprocess,os,re,datetime
P=Path('/workspace/rectangle-clt-singular/lean-rectangle-clt-arxiv-v1')
E=P/'evidence/actual-h-fourth-printed/checkpoint-1'; E.mkdir(parents=True,exist_ok=True)
F=Path('RectangleCLTArxivV1/ActualHFourthPrinted.lean')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
targets=['RectangleCLTArxivV1.'+n for n in re.findall(r'^(?:theorem|def|lemma)\s+([A-Za-z0-9_]+)',(P/F).read_text(),re.M)]
assert len(targets)==5
arr='#[\n    '+',\n    '.join('``'+n for n in targets)+']'
imports='import RectangleCLTArxivV1.ActualHFourthPrinted\n'
template=(P/'evidence/actual-h-corollaries/checkpoint-1/Audit.lean').read_text()
start=template.index('  let targets :=');end=template.index('  let allowed :=',start)
audit=imports+template[template.index('import Lean.Util.CollectAxioms'):start]+'  let targets := '+arr+'\n'+template[end:]
(E/'Audit.lean').write_text(audit)
template=(P/'evidence/actual-h-corollaries/checkpoint-1/Types.lean').read_text()
start=template.index('  let targets :=');end=template.index('  let mut queue',start)
types=imports+template[template.index('import Lean.Util.CollectAxioms'):start]+'  let targets := '+arr+'\n'+template[end:]
types=types.replace('Actual supplier-free H3 finite expectation and Corollaries4/5 with raw normalized source time-L1/integrated budget','Printed fixed-b H3 bandwidth constant and actual finite fourth-derivative expectation')
(E/'Types.lean').write_text(types)
script=E/'run.py'
if script.resolve()!=Path(__file__).resolve():script.write_text(Path(__file__).read_text())
bound=[F,E.relative_to(P)/'Audit.lean',E.relative_to(P)/'Types.lean',E.relative_to(P)/'run.py',Path('lakefile.toml'),Path('lake-manifest.json'),Path('lean-toolchain')]
parent_ledger=Path('correspondence/actual-h-corollaries-passages.json')
parent_freeze=Path('evidence/actual-h-corollaries/source-freeze.json')
ident={str(f):sha(P/f) for f in bound}
parent_ident={str(f):sha(P/f) for f in [parent_ledger,parent_freeze]}
freeze=json.loads((P/parent_freeze).read_text())
for f,h in freeze['sources'].items():assert sha(P/f)==h
run={'scope':'Exact printed fixed-b H3 width wrapper: positive A_b=max(1,b*restorationBandwidthConstant(actualMatrixConstant C0)) fixed before data; A_b*delta<=h implies both native width conditions; actual conditional Gaussian fourth-derivative L1 and finite expectation bound with no analytic estimate supplier.','status':'running','release_wide_certification':False,'started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'source_identity':ident,'parent_packet_identity':parent_ident,'targets':targets,'commands':[]}
receipt=E/'run.json';env=dict(os.environ,PATH='/workspace/lean-toolchain-bin/bin:'+os.environ['PATH'])
def cmd(label,argv):
 row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str((E/(label+'.log')).relative_to(P))};run['commands'].append(row);receipt.write_text(json.dumps(run,indent=2)+'\n')
 with (P/row['log']).open('w') as out:r=subprocess.run(argv,cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
 row.update(exit_code=r.returncode,finished_at_utc=now(),log_sha256=sha(P/row['log']));receipt.write_text(json.dumps(run,indent=2)+'\n')
 if r.returncode:raise RuntimeError(label)
try:
 cmd('01-build',['lake','build','RectangleCLTArxivV1.ActualHFourthPrinted'])
 cmd('02-force',['lake','env','lean',str(F),'-o','.lake/build/lib/lean/RectangleCLTArxivV1/ActualHFourthPrinted.olean'])
 cmd('03-audit',['lake','env','lean',str((E/'Audit.lean').relative_to(P))])
 ad=json.loads((E/'03-audit.log').read_text());assert ad['all_axioms_allowed'] and len(ad['targets'])==5
 cmd('04-types-dependencies',['lake','env','lean',str((E/'Types.lean').relative_to(P))])
 td=json.loads((E/'04-types-dependencies.log').read_text());assert len(td['endpoints'])==5
 endpoints={x['name']:x for x in td['endpoints']};graph={x['name']:x['direct_project_dependencies'] for x in td['project_dependency_graph']}
 head='RectangleCLTArxivV1.lemma_H3_fourth_derivative';ty=endpoints[head]['expanded_type']
 for token in ['MatrixEstimates','matrix_suppliers','hδh','hRh','hR :']:assert token not in ty,token
 for token in ['theoremH3BandwidthConstant','ConditionalEventIndependence','IntrinsicRectangleConcentration']:assert token in ty,token
 pending=[head];seen=set()
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n);pending.extend(graph.get(n,[]))
 for n in ['theorem_H3_fourth_derivative','theoremH3BandwidthConstant_controls_width','proposition_H1_cubic_matrix_shifted','proposition_H2_pair_matrix_shifted']:assert 'RectangleCLTArxivV1.'+n in seen,n
 (E/'actual-route-assertions.json').write_text(json.dumps({'status':'passed','headline':head,'no_matrix_or_analytic_estimate_supplier':True,'printed_fixed_b_width_only':True,'original_conditional_model_and_concentration_retained':True,'actual_cubic_pair_and_scalar_width_routes':True,'headline_project_dependency_nodes':len(seen)},indent=2)+'\n')
 assert ident=={str(f):sha(P/f) for f in bound}
 assert parent_ident=={str(f):sha(P/f) for f in [parent_ledger,parent_freeze]}
 for f,h in freeze['sources'].items():assert sha(P/f)==h
 run.update(status='passed',public_declarations_audited=5,expanded_types=5,project_dependency_nodes=len(td['project_dependency_graph']),finished_at_utc=now(),final_source_identity={str(f):sha(P/f) for f in bound})
except Exception as e:run.update(status='failed',failure=str(e),finished_at_utc=now());raise
finally:receipt.write_text(json.dumps(run,indent=2)+'\n')
print(json.dumps({k:run[k] for k in ['status','public_declarations_audited','expanded_types','project_dependency_nodes']}))

from pathlib import Path
import datetime,hashlib,json
P=Path('/workspace/rectangle-clt-singular/lean-rectangle-clt-arxiv-v1')
Old=P/'evidence/exceptional-corollary-assembly/checkpoint-1'
E=P/'evidence/exceptional-corollary-assembly/checkpoint-2';E.mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((Old/'run.json').read_text())
assert r['status']=='failed' and r['failure']=='hasDerivAt_normalizedSeededExpectation'
assert all(c['exit_code']==0 for c in r['commands'])
assert all(sha(P/p)==h for p,h in r['source_identity'].items()),'Frozen source drift'
a=json.loads((Old/'14-audit.log').read_text());td=json.loads((Old/'15-types-dependencies.log').read_text())
assert a['all_axioms_allowed'] and len(a['targets'])==len(td['endpoints'])==34
assert all(set(x['transitive_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['targets'])
names={x['name'] for x in td['project_dependency_graph']}
required=['exceptional_seeded_separated_eq_cutoff_product','exceptionalFourth_cutoff_expectation_bound_of_matrix_suppliers','cap_seededFourthRemainder_exceptional_split','cap_seeded_exceptional_remainder_bound','exceptional_integral_minimum_add_constant','cap_time_increment_le','exceptionalBudget_rate_of_small_bandwidth_estimate','exceptionalBudgetRate_eq_printed','exceptionalBudgetRate_le_coefficient','exceptionalBudget_trivial_large_envelope','intrinsicBoundaryCoefficient_le_gaussian']
required=['RectangleCLTArxivV1.'+n for n in required]+['RectangleCLT.Companion.SplitV4.hasDerivAt_normalizedSeededExpectation']
assert all(n in names for n in required)
forbidden=['RectangleCLTArxivV1.'+n for n in ['hFourth_copy_pair_zero_outside_gap','hFourth_gap_or_parallel','positiveGap_CLT_of_matrix_suppliers','positiveGap_boundary_CLT_of_matrix_suppliers']]
assert not set(forbidden)&names
g={x['name']:x['direct_project_dependencies'] for x in td['project_dependency_graph']}
pending=['RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates'+s for s in ['', '.mk','.cubic','.pair']]+['RectangleCLTArxivV1.ExceptionalNormalizedMatrixEstimates'];seen=set()
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n);pending.extend(g.get(n,[]))
bad=[n for n in seen if any(token in n for token in ['Remainder','rectangleDistance','normalizedSeededExpectation','cap_time_increment','_CLT_'])]
assert not bad,bad
assert len(seen)==58
check={'status':'passed','required_actual_routes':required,'forbidden_global_gap_routes':forbidden,'supplier_definition_closure_nodes':len(seen),'supplier_definition_closure':sorted(seen),'supplier_target_bounds_found':bad}
(E/'actual-route-assertions.json').write_text(json.dumps(check,indent=2)+'\n')
validator=E/'validate.py';validator.write_text(Path(__file__).read_text())
out={**r,'status':'passed','failure':None,'scope':r['scope'],'started_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'execution_reused_from':str((Old/'run.json').relative_to(P)),'prior_fixture_failure':{'receipt':str((Old/'run.json').relative_to(P)),'sha256':sha(Old/'run.json'),'reason':'All build/force/strict34/fulltype commands exited0. The post-export fixture wrongly placed hasDerivAt_normalizedSeededExpectation in RectangleCLTArxivV1; the actual existing theorem is RectangleCLT.Companion.SplitV4.hasDerivAt_normalizedSeededExpectation. This validator corrects only that namespace and revalidates unchanged source and kernel exports.'},'public_declarations_audited':34,'expanded_types':34,'project_dependency_nodes':len(names),'actual_route_assertions':{'path':str((E/'actual-route-assertions.json').relative_to(P)),'sha256':sha(E/'actual-route-assertions.json')},'validator':{'path':str(validator.relative_to(P)),'sha256':sha(validator)},'final_source_identity':{p:sha(P/p) for p in r['source_identity']},'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(E/'run.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'passed','strict_targets':34,'expanded_types':34,'project_dependency_nodes':len(names),'supplier_closure_nodes':58,'receipt':str((E/'run.json').relative_to(P))}))

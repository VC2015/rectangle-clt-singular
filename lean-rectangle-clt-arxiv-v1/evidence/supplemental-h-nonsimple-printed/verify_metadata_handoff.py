"""Read-only guards for the unapplied H.1 nonsimple metadata proposal."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parents[2]
E=P/'evidence/supplemental-h-nonsimple-printed'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def at(d,p):
    for k in p.split('/')[1:]:
        k=k.replace('~1','/').replace('~0','~')
        d=d[int(k)] if isinstance(d,list) else d[k]
    return d
m=load(E/'metadata-input-manifest.json');q=load(E/'metadata-supersession-proposal.json')
assert q['status']=='prepared_not_applied'
assert sha(P/q['baseline_manifest']['path'])==q['baseline_manifest']['sha256']
for p,h in m['baseline_global_preimage_sha256'].items():assert sha(P/p)==h,p
for p,h in m['immutable_old_frozen_passage_ledgers'].items():assert sha(P/p)==h,p
assert len(m['immutable_old_frozen_passage_ledgers'])==75
for r in m['immutable_old_final_acceptance_inputs'].values():assert sha(P/r['path'])==r['sha256'],r['path']
r=m['immutable_old_pre_acceptance_manifest']['manifest'];assert sha(P/r['path'])==r['sha256']
for p,h in m['new_available_support_receipts'].items():assert sha(P/p)==h,p
cache={}
for r in q['current_assertion_fields']:
    if r['path'] not in cache:cache[r['path']]=load(P/r['path'])
    d=cache[r['path']]
    s=at(d,r['json_pointer']);assert s==r['current_value']
    assert hashlib.sha256(s.encode()).hexdigest()==r['current_value_sha256']
for r in q['historical_scope_fields_to_preserve']:
    assert at(cache[r['path']],r['json_pointer'])==r['current_value']
assert len(q['current_assertion_fields'])==54
assert len(q['historical_scope_fields_to_preserve'])==15
A=cache['correspondence/final-acceptance.json'];C=cache['correspondence/final-coverage.json'];S=cache['correspondence/statements.json']
assert A['frozen_passage_ledgers']==C['frozen_passage_ledgers']==m['immutable_old_frozen_passage_ledgers']
assert A['counts']=={'unqualified_statements':39,'qualified_statements':1,'excluded_conjectures':1,'proof_environments':34}
assert A['coverage_counts']['all_exact_mapped_declarations']==1949
assert not A['release_wide_unqualified_certification'] and not A['every_literal_printed_internal_claim_certified']
assert S['statements'][36]['id']=='S-hgap-lem-surfaces'
assert 'E.1' in S['statements'][25]['statement'] and 'qualification' in S['statements'][25]
assert 'Conjecture' in S['statements'][14]['statement']
print(json.dumps({'status':'PASS_PROPOSAL_INTEGRITY_ONLY','global_preimages':7,'stale_current_fields':54,'preserved_historical_fields':15,'unchanged_old_frozen_ledgers':75,'new_support_receipt_refs':len(m['new_available_support_receipts']),'pending_completion_gates':len(m['pending_completion_gates']),'existing_global_files_mutated':False,'Lean_commands_run':False},indent=2))

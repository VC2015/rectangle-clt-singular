#!/usr/bin/env python3
"""Register29 reviewed early proof units, without any q0 derivative claim."""
import datetime,hashlib,shutil
from record_transfers_lower_acceptance import PROJECT,HERE,read,sha,rel,write
O=PROJECT/'evidence/early-correspondence';B=O/'pre-acceptance-ledgers';N='RectangleCLTArxivV1.'
FILES=['c1-bounded-passages.json','c1-gaussian-passages.json','corollary-1-normalization-passages.json','lemma-2-smoothing-passages.json']

def main():
 freeze=read(O/'source-freeze.json');assert freeze['status']=='passed'
 for p,h in freeze['source_sha256'].items():assert sha(PROJECT/p)==h,p
 for p,h in freeze['reviewed_additional_source_sha256'].items():assert sha(PROJECT/p)==h,p
 for p,h in freeze['artifacts_sha256'].items():assert sha(PROJECT/p)==h,p
 run=read(O/'checkpoint-1/run.json');support=read(O/'support-checkpoint-1/run.json');assert run['status']==support['status']=='passed'
 assert read(O/'dependency-check.json')['status']=='passed'
 cleanpath=PROJECT/'evidence/supplement-g-clean-checkpoint/run.json';clean=read(cleanpath);assert clean['status']=='passed' and not clean['initial_git_status']
 for p,h in clean['source_identity']['files'].items():assert sha(PROJECT/p)==h,p
 for p,h in freeze['source_sha256'].items():
  if p.startswith('RectangleCLTArxivV1/'):assert clean['source_identity']['files'][p]==h,p
 for cmd in run['commands']:assert cmd['exit_code']==0 and sha(PROJECT/cmd['log'])==cmd['log_sha256']
 assert sha(O/'support-checkpoint-1/types-and-audit.log')==support['log_sha256']
 D=read(O/'expanded-types.json');E={r['name']:r for r in D['endpoints']};G={r['name']:r['direct_project_dependencies'] for r in D['project_dependency_graph']};assert len(E)==124
 B.mkdir(exist_ok=True)
 for f in [*FILES,'statements.json','proof-environments.json']:
  if not (B/f).exists():shutil.copyfile(HERE/f,B/f)
 if not (B/'STATUS.md').exists():shutil.copyfile(PROJECT/'STATUS.md',B/'STATUS.md')
 base=read(B/'statements.json')['summary']
 build={'path':rel(O/'checkpoint-1/run.json'),'sha256':sha(O/'checkpoint-1/run.json'),'status':'passed','scope':'Fresh selected-source build and forced replay in current hashed working checkout; this is not an initially clean working checkout.','initial_checkout_clean':False,'source_commit':run['source_commit'],'clean_exported_source_baseline':{'path':rel(cleanpath),'sha256':sha(cleanpath),'source_commit':clean['source_commit'],'new_namespace_sources_byte_identical':True}}
 audit={'run':rel(O/'checkpoint-1/run.json'),'log':rel(O/'checkpoint-1/types-and-strict-audit.log'),'log_sha256':sha(O/'checkpoint-1/types-and-strict-audit.log'),'support_receipt':{'path':rel(O/'support-checkpoint-1/run.json'),'sha256':sha(O/'support-checkpoint-1/run.json')},'allowed_axioms':['propext','Classical.choice','Quot.sound'],'full_type_count':124,'project_dependency_nodes':len(G),'dependency_check':{'path':rel(O/'dependency-check.json'),'sha256':sha(O/'dependency-check.json')}}
 def expanded(ns):
  assert set(ns)<=E.keys(),set(ns)-E.keys()
  return [{'declaration':n,'expanded_type':E[n]['expanded_type'],'export':rel(O/'expanded-types.json')} for n in ns]
 def deps(ns):return [{'declaration':n,'direct_dependencies':E[n]['direct_dependencies'],'direct_project_dependencies':G[n],'transitive_project_graph':rel(O/'expanded-types.json')} for n in ns]
 variations={'C1.B.7','C1.K.1','C1.K.2','C1.G.1','C1.G.4'};rows=[]
 for f in FILES:
  d=read(B/f)
  for r in d['passages']:
   ns=r.get('checked_declarations',r['archived_declaration_candidates']+r['new_declarations']);ns=list(dict.fromkeys(ns));assert ns
   q=PROJECT.parent/r['location']['path'];a,b=r['location']['lines'];assert hashlib.sha256(b''.join(q.read_bytes().splitlines(keepends=True)[a-1:b])).hexdigest()==r['location']['sha256']
   review=r['reading_order_review'];v=read(PROJECT/review);assert v['result'].startswith('PASS') and not v.get('unmatched_steps_in_selected_scope')
   r.setdefault('acceptance_status_history',[]).append(r['status']);r.update(status='checked_with_documented_route_variation' if r['id'] in variations else 'checked_printed_proof',new_declarations=ns,expanded_types=expanded(ns),dependency_bindings=deps(ns),clean_build_receipt=build,transitive_axiom_receipt=audit,reading_order_reviews=[{'path':review,'sha256':sha(PROJECT/review),'result':v['result']}]);rows.append({'id':r['id'],'ledger':'correspondence/'+f,'location':r['location'],'status':r['status'],'declarations':ns})
  d.update(accepted_selected_scope='Source/PDF/type review of the explicitly mapped early passages; no q0 derivative correspondence or whole-release claim.',pre_acceptance_ledger={'path':rel(B/f),'sha256':sha(B/f)},accepted_source_freeze={'path':rel(O/'source-freeze.json'),'sha256':sha(O/'source-freeze.json')});write(HERE/f,d)
 statements=read(B/'statements.json');group={'S-lem-concentration':[r['id'] for r in rows if r['id'].startswith('C1.')],'S-cor-observations':[r['id'] for r in rows if r['id'].startswith('COR1.')],'S-lem-endpoint':[r['id'] for r in rows if r['id'].startswith('LEM2.')]}
 for r in statements['statements']:
  if r['id'] in group:
   r['detailed_internal_passage_ids']=group[r['id']];r['detailed_passage_receipt']=audit;r['detailed_passage_scope']='Selected actual proof correspondence; earlier Rademacher unique-gradient/edge/perturbation subdivision and q0 derivative correspondence are not claimed here.'
 proofs=read(B/'proof-environments.json')
 for r in proofs['proof_environments']:
  if r['id'] not in ['P-main-02','P-main-11']:continue
  ids=[x['id'] for x in rows if x['id'].startswith('LEM2.')] if r['id']=='P-main-02' else [x['id'] for x in rows if x['id'].startswith(('C1.B.','C1.G.'))]
  r.update(status='checked_with_documented_route_variation' if r['id']=='P-main-11' else 'checked_printed_proof',passage_ids=ids,build_receipt=build,audit_receipt=audit,scope_qualification='Actual clock/endpoint or bounded/Gaussian proof uses only; no claim about earlier q0 derivative correspondence.')
 assert len(rows)==29
 statements['summary'].update(new_accepted_passage_correspondences=base['new_accepted_passage_correspondences']+29,accepted_passages_with_documented_route_variation=base['accepted_passages_with_documented_route_variation']+len(variations))
 assert statements['summary']['new_accepted_statement_correspondences']==33
 write(HERE/'statements.json',statements);write(HERE/'proof-environments.json',proofs)
 rec={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'release_wide_certification':False,'scope':'29 early bounded/Gaussian concentration, normalization and genuine exponential-clock smoothing passages. No added named-statement count. No q0 derivative correspondence.','build':build,'audit':audit,'accepted_passages':rows,'additional_accepted_passages':29,'additional_documented_route_variations':len(variations),'summary':statements['summary'],'pre_acceptance_ledgers':{rel(p):sha(p) for p in B.glob('*.json')},'accepted_ledgers':{rel(HERE/f):sha(HERE/f) for f in [*FILES,'statements.json','proof-environments.json']},'remaining_named_statement_count':6,'qualified_E1_kept_separate':True}
 write(HERE/'early-passages-acceptance.json',rec);print(statements['summary'])
if __name__=='__main__':main()

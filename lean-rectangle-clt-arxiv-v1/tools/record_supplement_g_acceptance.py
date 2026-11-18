#!/usr/bin/env python3
"""Register the exact normalized G1 and covariance-rank G3 after clean checks.

Frozen reviewed originals remain in evidence/supplement-g-reviewed-ledgers.
Only G1/G3 statements and proof environments25/26 are promoted here.
"""
import datetime,hashlib,json,shutil,re
from pathlib import Path
from record_transfers_lower_acceptance import PROJECT,HERE,read,sha,rel,write
RUN=PROJECT/'evidence/supplement-g-clean-checkpoint/run.json'
MAP=PROJECT/'evidence/supplement-g-clean-mapping-complete/receipt.json'
BACK=PROJECT/'evidence/supplement-g-reviewed-ledgers'
N='RectangleCLTArxivV1.'

def main():
 run,mapping=read(RUN),read(MAP)
 for v in read(HERE/'statements.json')['source_files'].values():assert sha(PROJECT.parent/v['path'])==v['sha256']
 assert run['status']==mapping['status']=='passed'
 assert not run['initial_git_status'] and not mapping['initial_git_status']
 assert mapping['base_clean_checkpoint']['sha256']==sha(RUN)
 assert mapping['source_identity_unchanged']
 for p,h in run['source_identity']['files'].items():assert sha(PROJECT/p)==h,p
 for c in run['commands']:
  assert c['exit_code']==0,c['label'];assert sha(RUN.parent/c['log'])==c['log_sha256']
 assert sha(PROJECT/mapping['log'])==mapping['log_sha256']
 D=read(PROJECT/mapping['log']);E={x['name']:x for x in D['endpoints']};G={x['name']:x['direct_project_dependencies'] for x in D['project_dependency_graph']}
 assert len(E)==mapping['targets']
 assert not {'RectangleCLT.Companion.SplitV4.relativeFourthMomentCLT','RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists'}&G.keys()
 reviews={'g3':['evidence/supplement-g/independent-lower-review.json','evidence/supplement-g/independent-lower-subreview-restoration.json'],'g1':['evidence/supplemental-g-cap-main/independent-lower-review.json','evidence/supplemental-g-cap-normalized-remainder/independent-root-review.json','evidence/supplement-g/independent-lower-review.json']}
 for ps in reviews.values():
  for p in ps:
   d=read(PROJECT/p);assert 'pass' in (d.get('status','')+d.get('result','')).lower(),p
   assert not d.get('mathematical_or_type_gaps',[]) and not d.get('unmatched_headline_premises',[])
   for field in ['frozen_sources_sha256','ledger_bound_sources_sha256','independently_reviewed_root_sources_sha256','source_sha256']:
    for f,h in d.get(field,{}).items():
     if isinstance(h,str) and len(h)==64:assert sha(PROJECT/f)==h,(p,f)
 def reviewed(key):return [{'path':p,'sha256':sha(PROJECT/p),'result':'PASS'} for p in reviews[key]]
 build={'path':rel(RUN),'sha256':sha(RUN),'source_commit':run['source_commit'],'initial_checkout_clean':True,'source_digest':run['source_identity']['aggregate_sha256'],'status':'passed','commands':len(run['commands'])}
 c=next(c for c in run['commands'] if c['label']=='c2-audit');audit={'run':rel(RUN),'log':rel(RUN.parent/c['log']),'log_sha256':c['log_sha256'],'exit_code':0,'allowed_axioms':mapping['allowed_axioms'],'strict_passage_audit':{'path':rel(MAP),'sha256':sha(MAP),'targets':mapping['targets']}}
 def canonical(ns):return list(dict.fromkeys(n if n.startswith('RectangleCLT') else N+n for n in ns))
 def expanded(ns):
  ns=canonical(ns);assert set(ns)<=E.keys(),set(ns)-E.keys()
  return [{'declaration':n,'expanded_type':E[n]['expanded_type'],'export':mapping['log']} for n in ns]
 def dependencies(ns):return [{'declaration':n,'direct_dependencies':E[n]['direct_dependencies'],'direct_project_dependencies':G[n],'transitive_project_graph':mapping['log']} for n in canonical(ns)]
 def loc(doc,a,b):
  p='research-rectangle-clt-singular/Rectangle_CLT_'+('arXiv' if doc=='main' else 'Supplement')+'_2026-11-16.tex'
  text=(PROJECT.parent/p).read_bytes().splitlines(keepends=True)
  return {'source':doc,'path':p,'lines':[a,b],'sha256':hashlib.sha256(b''.join(text[a-1:b])).hexdigest()}
 def backup(path):
  dest=BACK/path.name
  if not dest.exists():shutil.copyfile(path,dest)
  return dest
 required=set()
 for filename,key in [('supplemental-g-cap-passages.json','mapped_declarations'),('supplemental-g-signed-restoration-passages.json','theorems')]:
  for row in read(HERE/filename)['passages']:required.update(canonical(row[key]))
 for row in read(HERE/'supplemental-g-complementary-passages.json')['source_connections']:required.update(canonical(row['theorems']))
 assert required<=E.keys(),required-E.keys()
 BACK.mkdir(exist_ok=True)
 for p in sorted(HERE.glob('supplemental-g-*-passages.json')):
  assert mapping['ledger_sha256'][rel(p)]==sha(p),p
  backup(p)
 for f in ['statements.json','proof-environments.json'] :backup(HERE/f)
 if not (BACK/'STATUS.md').exists():shutil.copyfile(PROJECT/'STATUS.md',BACK/'STATUS.md')
 base_summary=read(BACK/'statements.json')['summary'];accepted=[]
 def bind(row,names,key,location,variation=False):
  ns=canonical(names);row.setdefault('acceptance_status_history',[]).append(row.get('status',row.get('inclusion_status')))
  row.update(status='checked_with_documented_route_variation' if variation else 'checked_printed_proof',location=location,new_declarations=ns,expanded_types=expanded(ns),dependency_bindings=dependencies(ns),clean_build_receipt=build,transitive_axiom_receipt=audit,reading_order_reviews=reviewed(key))
  accepted.append({'id':row['id'],'status':row['status'],'source':location,'declarations':ns,'ledger':None})
 cap=read(BACK/'supplemental-g-cap-passages.json')
 for r in cap['passages']:
  bind(r,r['mapped_declarations'],'g1',loc(r['source_document'],*r['tex_lines']));accepted[-1]['ledger']='correspondence/supplemental-g-cap-passages.json'
 cap.update(clean_integrated_checkpoint=build,pre_acceptance_ledger={'path':rel(BACK/'supplemental-g-cap-passages.json'),'sha256':sha(BACK/'supplemental-g-cap-passages.json')},status='accepted_exact_normalized_G1_with_checked_mapped_passages')
 write(HERE/'supplemental-g-cap-passages.json',cap)
 signed=read(BACK/'supplemental-g-signed-restoration-passages.json')
 signed_variants={'angular-copy-moments','signed-common-base-restoration','independent-base-and-gaussian-averaging','actual-copy-single-and-large-angle-endpoints'}
 for r in signed['passages']:
  bind(r,r['theorems'],'g3',loc('supplement',*r['lines']),r['id'] in signed_variants);accepted[-1]['ledger']='correspondence/supplemental-g-signed-restoration-passages.json'
 signed.update(clean_integrated_checkpoint=build,pre_acceptance_ledger={'path':rel(BACK/'supplemental-g-signed-restoration-passages.json'),'sha256':sha(BACK/'supplemental-g-signed-restoration-passages.json')},status='accepted_actual_signed_restoration_mapped_passages',independent_review=reviewed('g3'))
 write(HERE/'supplemental-g-signed-restoration-passages.json',signed)
 comp=read(BACK/'supplemental-g-complementary-passages.json')
 for i,r in enumerate(comp['source_connections'],1):
  r.setdefault('id',f'G3.source-connection-{i}');bind(r,r['theorems'],'g3',loc('supplement',*r['lines']),i>=2);accepted[-1]['ledger']='correspondence/supplemental-g-complementary-passages.json'
 comp.update(clean_integrated_checkpoint=build,pre_acceptance_ledger={'path':rel(BACK/'supplemental-g-complementary-passages.json'),'sha256':sha(BACK/'supplemental-g-complementary-passages.json')},status='accepted_actual_covariance_rank_G3_with_checked_source_connections',independent_review=reviewed('g3'))
 ranknames=[N+'cap_seededFourthRemainder_rank_complementary_bound',N+'cap_seededFourthRemainder_rank_intervalIntegrable',N+'cap_seededFourthRemainder_rank_abs_intervalIntegrable']
 comp['checked_final_covariance_rank_endpoints']={'declarations':ranknames,'expanded_types':expanded(ranknames),'dependency_bindings':dependencies(ranknames),'build_receipt':build,'audit_receipt':audit}
 write(HERE/'supplemental-g-complementary-passages.json',comp)
 # Other five ledgers are audited support records, not additional passage atoms.
 for p in sorted(BACK.glob('supplemental-g-*-passages.json')):
  if p.name in ['supplemental-g-cap-passages.json','supplemental-g-signed-restoration-passages.json','supplemental-g-complementary-passages.json']:continue
  d=read(p);ns=[]
  def gather(v):
   if isinstance(v,str) and (re.fullmatch(r'RectangleCLTArxivV1\.[A-Za-z0-9_]+',v) or re.fullmatch(r'cap[A-Za-z0-9_]+',v)):ns.append(v)
   elif isinstance(v,list):
    for z in v:gather(z)
   elif isinstance(v,dict):
    for z in v.values():gather(z)
  gather(d)
  if not ns and p.name=='supplemental-g-seeded-base-passages.json':ns=[N+'capSignedProjection_hypotheses',N+'cap_original_single_face_mass',N+'cap_original_pair_face_mass']
  ns=canonical(ns);assert ns,(p,'No selected support names')
  d['clean_support_binding']={'scope':'Checked declaration support for final G3; not an additional accepted named statement or passage atom.','expanded_types':expanded(ns),'dependency_bindings':dependencies(ns),'build':build,'audit':audit,'reading_order_reviews':reviewed('g3')}
  d['pre_acceptance_ledger']={'path':rel(p),'sha256':sha(p)};write(HERE/p.name,d)
 statements=read(BACK/'statements.json')
 endpointmap={'S-prop-dimension-cap':('g1',[N+'proposition_G1_dimension_log_cap_normalized']),'S-lem-cap-remainder':('g3',ranknames)}
 for r in statements['statements']:
  if r['id'] not in endpointmap:continue
  key,ns=endpointmap[r['id']];r.update(status='proved_and_freshly_checked',lean_declarations=ns,expanded_types=expanded(ns),dependency_declarations=dependencies(ns),build_receipt=build,audit_receipt=audit,reading_order_reviews=reviewed(key),printed_proof_status='checked_mapped_passages_with_explicit_method_notes')
  if key=='g1':r['normalization_convention']='The public endpoint is proposition_G1_dimension_log_cap_normalized: exact printed normalized fourth remainder; the unrescaled raw integral in the older public theorem is an auxiliary valid result.'
 proofs=read(BACK/'proof-environments.json')
 for r in proofs['proof_environments']:
  if r['id'] not in ['P-supplement-25','P-supplement-26']:continue
  key='g3' if r['id']=='P-supplement-25' else 'g1';ids=[x['id'] for x in accepted if ('g-cap' in x['ledger'])==(key=='g1')]
  r.update(status='checked_with_documented_route_variation' if key=='g3' else 'checked_printed_proof',passage_ids=ids,build_receipt=build,audit_receipt=audit,reading_order_reviews=reviewed(key))
 variations=sum(x['status']=='checked_with_documented_route_variation' for x in accepted)
 statements['summary'].update(new_accepted_statement_correspondences=sum(x['status']=='proved_and_freshly_checked' for x in statements['statements']),new_accepted_passage_correspondences=base_summary['new_accepted_passage_correspondences']+len(accepted),accepted_passages_with_documented_route_variation=base_summary['accepted_passages_with_documented_route_variation']+variations)
 assert len(accepted)==31 and statements['summary']['new_accepted_statement_correspondences']==33
 write(HERE/'statements.json',statements);write(HERE/'proof-environments.json',proofs)
 openids=[x['id'] for x in statements['statements'] if x.get('status')=='open'];assert len(openids)==6,openids
 record={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'release_wide_certification':False,'scope':'Exact normalized G1 and actual covariance-rank G3;19 cap units+7 signed-restoration units+5 source connections. Other five G ledgers are checked supports without double counting.','build':build,'audit':audit,'mapped_endpoint_count':len(E),'project_dependency_nodes':len(G),'accepted_passages':accepted,'additional_accepted_passages':31,'additional_route_variation_units':variations,'summary':statements['summary'],'remaining_named_statements':openids,'qualified_E1_counted_separately':True,'pre_acceptance_ledger_sha256':{rel(p):sha(p) for p in BACK.glob('*.json')},'accepted_ledger_sha256':{rel(p):sha(p) for p in [HERE/'statements.json',HERE/'proof-environments.json',*sorted(HERE.glob('supplemental-g-*-passages.json'))]}}
 write(HERE/'supplement-g-acceptance.json',record);print(json.dumps({'summary':statements['summary'],'remaining_named_statements':openids,'mapped_endpoints':len(E),'project_nodes':len(G)},indent=2))
if __name__=='__main__':main()

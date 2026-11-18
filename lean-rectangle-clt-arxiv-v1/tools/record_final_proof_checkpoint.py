"""Record exact frozen final proof packets before their separate clean audit.

This prepares a reviewable staging inventory. It does not stage, commit, alter
proof files, or register any statement/passage as accepted.
"""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,re,subprocess

R=Path(__file__).resolve().parents[1]
O=R/'evidence/final-proof-checkpoint'
S=json.loads((O/'selection.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def local(p):return str(p.relative_to(R))
def recorded_status(d):return d.get('status',d.get('result','passed_bool' if d.get('passed') is True else 'HISTORICAL_NO_STATUS_FIELD'))
def passed(d):return str(recorded_status(d)).lower().startswith('pass')

artifacts={p for d in S['evidence_directories'] for p in (R/'evidence'/d).rglob('*')
  if p.is_file() and p.suffix!='.pyc' and '__pycache__' not in str(p)}
artifacts|={R/'correspondence'/(n+'.json') for n in S['ledgers']}
required=[]
for f in S['required_completed_reviews']+S['required_passed_receipts']:
 p=R/f;assert p.is_file(),('Required final record not ready',f)
 d=json.loads(p.read_text());assert passed(d),(f,recorded_status(d))
 assert p in artifacts,f
 required.append({'path':f,'sha256':sha(p),'status':recorded_status(d)})

claims={};frozen_claims={};receipts=[];reviews=[];log_count=0
def collect(d,path,dest):
 if isinstance(d,dict):
  for k,v in d.items():
   if k.startswith('RectangleCLTArxivV1/') and k.endswith('.lean') and isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v):
    dest.setdefault(k,{}).setdefault(v,[]).append(path)
   collect(v,path,dest)
 elif isinstance(d,list):
  for v in d:collect(v,path,dest)

def verify_logs(d,path):
 global log_count
 if isinstance(d,dict):
  if isinstance(d.get('log'),str) and d.get('log_sha256'):
   p=R/d['log'];assert p.is_file(),(path,d['log'])
   assert sha(p)==d['log_sha256'],(path,d['log']);log_count+=1
  for x in d.values():verify_logs(x,path)
 elif isinstance(d,list):
  for x in d:verify_logs(x,path)

for p in sorted(artifacts):
 if p.suffix!='.json':continue
 d=json.loads(p.read_text());collect(d,local(p),claims);verify_logs(d,local(p))
 if not isinstance(d,dict):continue
 if p.name in ('run.json','receipt.json'):
  receipts.append({'path':local(p),'sha256':sha(p),'status':recorded_status(d)})
 if p.name=='source-freeze.json' or (p.name in ('run.json','receipt.json') and passed(d)):
  collect(d,local(p),frozen_claims)
 if 'review' in p.name or 'review' in str(p.parent):
  if any(k in d for k in ['reviewer','review_kind','reviewed_at_utc','result','status']):
   reviews.append({'path':local(p),'sha256':sha(p),'status':recorded_status(d)})

spec=importlib.util.spec_from_file_location('mapper',R/'tools/prepare_full_clean_mapping.py')
mapper=importlib.util.module_from_spec(spec);spec.loader.exec_module(mapper)
modules,_=mapper.modules_and_declarations(R)
all_modules,missing=mapper.imported_modules(modules,['RectangleCLTArxivV1']+S['extra_imports'])
assert not missing,missing
proofs={local(modules[m]) for m in all_modules if m.startswith('RectangleCLTArxivV1.')}
tracked=set(subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD','--','.'],cwd=R,text=True).splitlines())
source_hashes={p:sha(R/p) for p in sorted(proofs)}
new_sources=sorted(proofs-tracked)
for p in new_sources:
 assert source_hashes[p] in frozen_claims.get(p,{}),('New imported proof lacks completed receipt/freeze identity',p)
historical={p:{h:ps for h,ps in claims.get(p,{}).items() if h!=source_hashes[p]}
  for p in proofs if any(h!=source_hashes[p] for h in claims.get(p,{}))}
integrated={p:sha(R/p) for p in S['integrated_files']}
tools={p:sha(R/p) for p in S['completed_tool_files']}
put(O/'source-manifest.json',{'scope':'Exact final ArxivV1 Root/extra import source closure plus separately identified integrated Root/Audit/dependency files. Global acceptance is unchanged.','proof_source_sha256':source_hashes,'new_proof_sources':new_sources,'matching_completed_identity_witnesses':{p:frozen_claims[p][source_hashes[p]] for p in new_sources},'preserved_historical_source_identities':historical,'integrated_file_sha256':integrated,'tool_sha256':tools,'pinned_external_source_sha256':{os.path.relpath(modules[m],R):sha(modules[m]) for m in sorted(all_modules) if not m.startswith('RectangleCLTArxivV1')}})
put(O/'artifact-manifest.json',{'scope':'Selected complete frozen packets and reviews, including original failure fixtures and provisional mapping plans. Their individual scopes and statuses are preserved.','artifact_sha256':{local(p):sha(p) for p in sorted(artifacts)},'receipts':receipts,'reviews':reviews})
self_files={'tools/record_final_proof_checkpoint.py'}|{'evidence/final-proof-checkpoint/'+n for n in ['selection.json','source-manifest.json','artifact-manifest.json','checkpoint.json','README.md','stage-files.txt']}
paths={local(p) for p in artifacts}|set(new_sources)|set(integrated)|set(tools)|self_files
assert not set(S['exclude_exact_paths'])&paths
assert all((R/p).is_file() for p in paths if p not in self_files),sorted(p for p in paths if not (R/p).is_file())
(O/'stage-files.txt').write_text('\n'.join(sorted(paths))+'\n')
put(O/'checkpoint.json',{'status':'FROZEN_FINAL_PROOF_SOURCE_EVIDENCE_CHECKPOINT','created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'scope':S['scope_note'],'proof_source_count':len(proofs),'new_proof_source_count':len(new_sources),'artifact_count':len(artifacts),'stage_count':len(paths),'required_passed_records':required,'receipt_count':len(receipts),'review_record_count':len(reviews),'verified_hash_bound_log_references':log_count,'preserved_failed_receipts':[x for x in receipts if str(x['status']).lower().startswith('fail')],'historical_current_source_mismatch_count':len(historical),'source_manifest_sha256':sha(O/'source-manifest.json'),'artifact_manifest_sha256':sha(O/'artifact-manifest.json'),'stage_inventory_sha256':sha(O/'stage-files.txt'),'explicit_exclusions':S['exclude_exact_paths'],'qualifications':['Raw H3/Cor4/Cor5 and canonical/fixed-b wrappers are preserved with their exact independent review scopes.','The shared-union mapper has focused tests and independent tooling reviews; provisional plans are not a final clean audit. Regenerate after this proof commit.','No new STATUS/global statement/proof-environment acceptance is performed in this checkpoint.','Historical lower scalar Berry--Esseen reuse of the checked foundation bounded CLT remains disclosed; actual new headline closures have separate endpoint-specific independence checks.']})
print(json.dumps({'sources':len(proofs),'new_sources':len(new_sources),'artifacts':len(artifacts),'stage_files':len(paths),'required_records':len(required),'receipts':len(receipts),'reviews':len(reviews),'historical_source_mismatches':len(historical)}))

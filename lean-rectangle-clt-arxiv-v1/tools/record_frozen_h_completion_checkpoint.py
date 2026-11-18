"""Package frozen supporting H/I sources and evidence; no headline acceptance."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[1];O=R/'evidence/frozen-h-completion-checkpoint'
SELECT=json.loads((O/'selection.json').read_text())
DIRS=SELECT['evidence_directories']
LEDGERS=SELECT['ledgers']
FORBIDDEN=SELECT['exclude_source_prefixes']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def local(p):return str(p.relative_to(R))
def allowed(p):return not any(s in p for s in FORBIDDEN)
artifacts={f for n in DIRS for f in (R/'evidence'/n).rglob('*') if f.is_file() and allowed(local(f)) and f.suffix!='.pyc' and '__pycache__' not in str(f)}
artifacts|={R/'correspondence'/(n+'.json') for n in LEDGERS}
assert all(f.exists() for f in artifacts)
prerequisites=[]
for p in SELECT['source_inventory_prerequisite_manifests']:
 d=json.loads((R/p).read_text())
 for f,h in d['sha256'].items():assert sha(R/f)==h,(p,f)
 prerequisites.append({'path':p,'sha256':sha(R/p),'files':len(d['files'])})
required_reviews=[]
for p in SELECT['required_completed_reviews']:
 d=json.loads((R/p).read_text());status=d.get('status',d.get('result',''))
 assert str(status).lower().startswith('pass'),(p,status)
 assert R/p in artifacts,p
 required_reviews.append({'path':p,'sha256':sha(R/p),'status':status})
source_claims={};receipts=[];reviews=[]
def walk(d,p):
 if isinstance(d,dict):
  for k,v in d.items():
   if k.startswith('RectangleCLTArxivV1/') and k.endswith('.lean') and isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v) and allowed(k):
    source_claims.setdefault(k,{}).setdefault(v,[]).append(p)
   walk(v,p)
 elif isinstance(d,list):
  for x in d:walk(x,p)
for f in sorted(artifacts):
 if f.suffix!='.json':continue
 d=json.loads(f.read_text());walk(d,local(f))
 if isinstance(d,dict):
  if f.name in ['run.json','receipt.json']:
   receipts.append({'path':local(f),'sha256':sha(f),'recorded_status':d.get('status',d.get('result','HISTORICAL_NO_STATUS_FIELD')),'scope':d.get('scope'),'command_count':len(d.get('commands',d.get('independent_commands',[])))})
  if 'review' in f.name or 'review' in str(f.parent):
   if any(k in d for k in ['reviewer','review_kind','reviewed_at_utc','result','status']):reviews.append({'path':local(f),'sha256':sha(f),'recorded_status':d.get('status',d.get('result'))})
# Validate every hash-bound command log, including preserved failed fixtures.
log_references=0
for f in sorted(artifacts):
 if f.suffix!='.json':continue
 def verify_logs(d):
  global log_references
  if isinstance(d,dict):
   if isinstance(d.get('log'),str) and d.get('log_sha256'):
    q=R/d['log'];assert q.is_file(),(local(f),d['log']);assert sha(q)==d['log_sha256'],(local(f),d['log']);log_references+=1
   for v in d.values():verify_logs(v)
  elif isinstance(d,list):
   for x in d:verify_logs(x)
 verify_logs(json.loads(f.read_text()))
# Ledger single-source records and source_files spelling, as well as all frozen
# receipt inventories, seed complete source/import closure.
for n in LEDGERS:
 p=R/'correspondence'/(n+'.json');d=json.loads(p.read_text())
 for key in ['source_identity','source_files']:
  for f,h in d.get(key,{}).items():
   if f.startswith('RectangleCLTArxivV1/') and f.endswith('.lean') and allowed(f):source_claims.setdefault(f,{}).setdefault(h,[]).append(local(p))
 if isinstance(d.get('source'),str) and d['source'].endswith('.lean'):
  source_claims.setdefault(d['source'],{}).setdefault(d['source_sha256'],[]).append(local(p))
seeds=set(source_claims);closure=set();imports={};boundary={};q=list(seeds)
while q:
 p=q.pop()
 if p in closure:continue
 assert allowed(p),p
 f=R/p;assert f.is_file(),p;closure.add(p)
 ns=re.findall(r'^import\s+([\w.]+)',f.read_text(),re.M)
 own=[n.replace('.','/')+'.lean' for n in ns if n.startswith('RectangleCLTArxivV1.')]
 assert all(allowed(x) for x in own),(p,own)
 imports[p]=own;boundary[p]=[n for n in ns if not n.startswith('RectangleCLTArxivV1.')];q+=own
tracked=set(subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD','--','.'],cwd=R,text=True).splitlines())
source_manifest={p:sha(R/p) for p in sorted(closure)}
missing=[p for p,h in source_manifest.items() if p not in tracked and h not in source_claims.get(p,{})]
assert not missing,('Uncommitted source lacks matching frozen evidence identity',missing)
# A current-matching source evidence witness is distinct from preserved old
# hashes/failed fixtures; those historical records are never rewritten.
witness={p:source_claims.get(p,{}).get(h,[]) for p,h in source_manifest.items()}
historical={p:{h:paths for h,paths in claims.items() if h!=source_manifest[p]} for p,claims in source_claims.items() if p in source_manifest and any(h!=source_manifest[p] for h in claims)}
put(O/'source-manifest.json',{'scope':'Frozen H surface/coarea/cubic and ordinary pair-family support, early internal proofs and conditional Cor5, including complete ArxivV1 import closure. No headline acceptance or final pair matrix claim.','source_sha256':source_manifest,'new_namespace_direct_imports':imports,'external_import_boundary':{p:ns for p,ns in boundary.items() if ns},'matching_frozen_identity_witnesses':witness,'preserved_historical_source_identities':historical,'new_files_count':sum(p not in tracked for p in closure),'already_tracked_import_sources_count':sum(p in tracked for p in closure),'package_configuration_sha256':{p:sha(R/p) for p in ['lakefile.toml','lake-manifest.json','lean-toolchain']}})
put(O/'artifact-manifest.json',{'scope':'Exact completed support packet evidence; preserves failed fixtures and frozen historical prose. Manifest includes original receipts/reviews without promoting their scope.','artifact_sha256':{local(p):sha(p) for p in sorted(artifacts)},'recorded_receipts':receipts,'recorded_reviews':reviews})
paths={local(p) for p in artifacts}|{p for p in closure if p not in tracked}|{'tools/record_frozen_h_completion_checkpoint.py','evidence/frozen-h-completion-checkpoint/source-manifest.json','evidence/frozen-h-completion-checkpoint/artifact-manifest.json','evidence/frozen-h-completion-checkpoint/checkpoint.json','evidence/frozen-h-completion-checkpoint/README.md','evidence/frozen-h-completion-checkpoint/selection.json','evidence/frozen-h-completion-checkpoint/stage-files.txt'}
assert all(allowed(p) for p in paths)
assert not any(p in SELECT['other_exclusions'] for p in paths)
(O/'stage-files.txt').write_text('\n'.join(sorted(paths))+'\n')
put(O/'checkpoint.json',{'status':'FROZEN_H_COMPLETION_SOURCE_EVIDENCE_CHECKPOINT','created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'scope':'Source/evidence preservation only, before final integrated audit. No named statement, proof-environment, passage acceptance, or STATUS update.','proof_source_count':len(closure),'uncommitted_proof_source_count':sum(p not in tracked for p in closure),'evidence_artifact_count':len(artifacts),'already_tracked_unchanged_artifact_count':sum(local(p) in tracked and subprocess.check_output(['git','show','HEAD:'+subprocess.check_output(['git','rev-parse','--show-prefix'],cwd=R,text=True).strip()+local(p)],cwd=R)==p.read_bytes() for p in artifacts),'verified_hash_bound_log_references':log_references,'recorded_receipts_count':len(receipts),'recorded_review_records_count':len(reviews),'preserved_failed_receipts':[x for x in receipts if str(x['recorded_status']).lower().startswith('fail')],'source_manifest_sha256':sha(O/'source-manifest.json'),'artifact_manifest_sha256':sha(O/'artifact-manifest.json'),'stage_inventory_sha256':sha(O/'stage-files.txt'),'explicit_exclusions':FORBIDDEN+SELECT['other_exclusions'],'validated_author_inventories':prerequisites,'required_completed_reviews':required_reviews,'scope_qualifications':['All-threshold H1 surface and cubic-final proofs are preserved as source/evidence packets only, without global headline registration.','Pair14/16/9 are frozen supporting reference/entropy/assembly lemmas; no completed final pair matrix, active pair trace or positive pair average is included. Independent-review state remains the exact original packet record.','Conditional Cor5 final CLT retains only the precise actual full cubic/full-angle matrix supplier; standalone literal-R4 integral exposes the actual concentration premise, with raw L1 unconditional on those suppliers.','Early B4/B5/E3 and lower15 have separate independent reviews. The lower scalar Berry--Esseen specialization from a checked foundation bounded CLT is expressly disclosed; no blanket old-CLT absence is claimed for that route.','Optional lower duplication is finite support only; no new dimensionrm+1 headline is claimed.','This is a selected frozen source/evidence checkpoint, not a clean combined whole-paper audit or acceptance-count update.','Failed source/type/metadata fixtures remain preserved beside the actual successful replacements, with their original statuses.']})
print(json.dumps({'source_count':len(closure),'new_sources':sum(p not in tracked for p in closure),'artifact_count':len(artifacts),'stage_count':len(paths),'receipts':len(receipts),'reviews':len(reviews),'historical_source_mismatches':len(historical),'failed_receipts':[x['path'] for x in receipts if str(x['recorded_status']).lower().startswith('fail')]}))

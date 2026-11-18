from pathlib import Path
import json,hashlib,datetime,subprocess,os
P=Path(__file__).resolve().parents[3];D=Path(__file__).resolve().parent
L=P/'correspondence/supplemental-h-active-face-reindex-passages.json';F=P/'evidence/supplement-h-active-face-reindex/source-freeze.json';l=json.loads(L.read_text());f=json.loads(F.read_text())
files=[P/k for k in l['source_identity']]+[L,F,P/'evidence/supplement-h-active-face-reindex/checkpoint-1/run.json',P/'evidence/supplement-h-active-face-reindex/checkpoint-1/expanded-types.json',D/'TypesAndAudit.lean',Path(__file__)]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ident=lambda:{str(p.relative_to(P)):sha(p) for p in files}
assert all(sha(P/k)==v for k,v in l['source_identity'].items());assert sha(L)==f['ledger']['sha256']
env=dict(os.environ);env['PATH']='/workspace/lean-toolchain-bin/bin:'+env.get('PATH','')
r={'scope':'Independent bounded_intrinsic review: exact active physical face enumeration, normals/projection, F pi theta transport, arbitrary signed first-face and all-tuple coefficients, positive-length empty-face selectors; no matrix/rate claim.','started_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_identity':ident(),'commands':[],'status':'running','setup_note':'First inline attempt could not find lake before setting toolchain PATH; no source elaboration ran. Retained setup-attempt-1.json.'}
def save(): (D/'run.json').write_text(json.dumps(r,indent=2)+'\n')
def run(label,cmd):
 row={'label':label,'argv':cmd,'cwd':str(P),'log':str((D/(label+'.log')).relative_to(P))};r['commands'].append(row);save()
 with (D/(label+'.log')).open('wb') as out:p=subprocess.run(cmd,cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
 row['exit_code']=p.returncode;row['log_sha256']=sha(D/(label+'.log'));save();assert p.returncode==0,label
 print(label,'PASS',flush=True)
try:
 run('01-build',['lake','build','RectangleCLTArxivV1.SupplementalHActiveFaceReindex'])
 run('02-force-source',['lake','env','lean','RectangleCLTArxivV1/SupplementalHActiveFaceReindex.lean'])
 run('03-types-and-strict15',['lake','env','lean',str((D/'TypesAndAudit.lean').relative_to(P))])
 ty=json.loads((D/'03-types-and-strict15.log').read_text());orig=json.loads((P/'evidence/supplement-h-active-face-reindex/checkpoint-1/expanded-types.json').read_text())
 assert len(ty['endpoints'])==15
 assert {x['name']:x['expanded_type'] for x in ty['endpoints']}=={x['name']:x['expanded_type'] for x in orig['endpoints']}
 assert {x['name'] for x in ty['endpoints']}==set(l['declarations'])
 assert ident()==r['source_identity'];r.update(status='passed',strict_targets=15,expanded_types=15,project_dependency_nodes=len(ty['project_dependency_graph']),source_identity_after=ident());save();print('Independent checkpoint PASS',flush=True)
except Exception as e:r.update(status='failed',error=str(e));save();raise

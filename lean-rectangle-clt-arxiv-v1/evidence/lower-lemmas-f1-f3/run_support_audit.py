import datetime,hashlib,json,os,subprocess
from pathlib import Path
PROJECT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent/'proof-step-audit-1';OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
base=PROJECT/'evidence/lower-lemmas-f1-f3/checkpoint-2/run.json';r=json.loads(base.read_text());assert r['status']=='passed'
x=json.loads((base.parent/'expanded-types.json').read_text());graph={v['name']:v['direct_project_dependencies'] for v in x['project_dependency_graph']}
todo=r['audit_targets'][:];seen=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(graph.get(n,[]))
names=[v['name'] for v in x['endpoints'] if v['name'] not in seen]
audit=OUT/'Audit.lean';audit.write_text('import RectangleCLTArxivV1.LowerLemmaF1Support\nimport RectangleCLTArxivV1.LowerLemmaF2\nimport RectangleCLTArxivV1.LowerLemmaF3\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n  let allowed := #[``propext,``Classical.choice,``Quot.sound]\n  let targets := #['+',\n    '.join('``'+n for n in names)+']\n  for target in targets do\n    let axs ← Lean.collectAxioms target\n    for ax in axs do\n      unless allowed.contains ax do\n        throwError "Unexpected axiom {ax} in {target}"\n    logInfo m!"{target} uses {axs.toList}"\n')
record={'scope':'Additional printed proof steps not already in the strict13 wrapper dependency closure; together the two audits cover all126 exported declarations transitively','source_sha256':r['source_sha256'],'base_receipt':str(base.relative_to(PROJECT)),'base_receipt_sha256':sha(base),'audit_targets':names,'expanded_type_count':len(x['endpoints']),'started_at_utc':now(),'status':'running'}
rec=OUT/'run.json';rec.write_text(json.dumps(record,indent=2)+'\n');env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
argv=['lake','env','lean',str(audit.relative_to(PROJECT))];record['argv']=argv
with (OUT/'audit.log').open('wb') as f:p=subprocess.run(argv,cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT)
record.update(exit_code=p.returncode,status='passed' if not p.returncode else 'failed',finished_at_utc=now(),audit_source_sha256=sha(audit),audit_log_sha256=sha(OUT/'audit.log'))
for src,digest in r['source_sha256'].items():assert sha(PROJECT/src)==digest
rec.write_text(json.dumps(record,indent=2)+'\n')
raise SystemExit(p.returncode)

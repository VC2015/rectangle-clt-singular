#!/usr/bin/env python3
import datetime,hashlib,importlib.util,json,os,subprocess
from pathlib import Path
P=Path(__file__).resolve().parents[3];D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('mapper',P/'tools/prepare_full_clean_mapping.py');mapper=importlib.util.module_from_spec(spec);spec.loader.exec_module(mapper)
targets=json.loads((D/'targets.json').read_text());mods=targets['modules'];modules,decls=mapper.modules_and_declarations(P)
closure,missing=mapper.imported_modules(modules,['RectangleCLTArxivV1.'+m for m in mods]);assert not missing,missing
assert not any('NonsimpleFaceCofaces' in m for m in closure)
files=list({modules[m] for m in closure})+[P/x for x in ['lakefile.toml','lake-manifest.json','lean-toolchain','tools/prepare_full_clean_mapping.py']]+[D/x for x in ['run.py','Audit.lean','Types.lean','targets.json']]
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();identity=lambda:{os.path.relpath(p,P):sha(p) for p in sorted(files)}
report={'scope':'Independent direct wrapper review and fresh verification; reviewer specified the wrapper approach and authored the independently-reviewed reused NormalCone support. Actual retained-family exact-presentation singleton supporting-normal positive-multiple theorem. Nonretained original constraints become the strict tautology 0<1, and the proved genuine outward normal-cone presentation theorem gives orientation and offset scaling. Cofaces and all surface/Green/integral claims excluded.','release_wide_certification':False,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'started_at_utc':now(),'source_identity':identity(),'owned_source_identity':{str((P/'RectangleCLTArxivV1'/f'{m}.lean').relative_to(P)):sha(P/'RectangleCLTArxivV1'/f'{m}.lean') for m in mods},'project_source_import_closure':sorted(closure),'commands':[],'status':'running'}
def save():(D/'run.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,argv):
 log=D/(label+'.log');row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str(log.relative_to(P))};report['commands'].append(row);save()
 with log.open('wb') as out:proc=subprocess.run(argv,cwd=P,stdout=out,stderr=subprocess.STDOUT,env=os.environ)
 row.update(exit_code=proc.returncode,log_sha256=sha(log),finished_at_utc=now());save()
 if proc.returncode:raise RuntimeError(label+' failed')
 print(label+' PASS',flush=True)
try:
 run('01-build',['lake','build']+['RectangleCLTArxivV1.'+m for m in mods])
 for j,m in enumerate(mods,2):run(f'{j:02d}-force-{m}',['lake','env','lean',f'RectangleCLTArxivV1/{m}.lean'])
 run('10-strict-public-audit',['lake','env','lean',str((D/'Audit.lean').relative_to(P))])
 audit=json.loads((D/'10-strict-public-audit.log').read_text());assert audit['all_axioms_allowed'];assert {r['name'] for r in audit['targets']}==set(targets['targets'])
 report['strict_public_declarations']=len(audit['targets'])
 run('11-fulltypes-project-graph',['lake','env','lean',str((D/'Types.lean').relative_to(P))])
 types=json.loads((D/'11-fulltypes-project-graph.log').read_text());assert {r['name'] for r in types['endpoints']}==set(targets['targets']);assert set(types['axiom_union'])<={'propext','Classical.choice','Quot.sound'}
 assert all('Cofaces' not in r['name'] for r in types['project_dependency_graph'])
 report.update(full_types=len(types['endpoints']),project_dependency_nodes=len(types['project_dependency_graph']),axiom_union=types['axiom_union'])
 assert identity()==report['source_identity'],'Frozen source or audit harness changed during checkpoint'
 report.update(status='passed',finished_at_utc=now(),source_identity_unchanged=True,final_source_identity=identity());save();print('checkpoint PASS',flush=True)
except Exception as e:
 report.update(status='failed',error=str(e),finished_at_utc=now());save();raise

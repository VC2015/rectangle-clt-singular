from pathlib import Path
import json,hashlib,subprocess,datetime,os,re
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
SOURCES=['RectangleCLTArxivV1/SupplementalHNonsimpleRidgeGreenActualMass.lean', 'RectangleCLTArxivV1/SupplementalHNonsimpleRidgeGreenCanonical.lean']
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
ns={'__name__':'leaf_mapper_helpers','__file__':str(ROOT/'tools/prepare_full_clean_mapping.py')}
exec(compile((ROOT/'tools/prepare_full_clean_mapping.py').read_text(),ns['__file__'],'exec'),ns)
modules,_=ns['modules_and_declarations'](ROOT)
mods=[p[:-5].replace('/','.')for p in SOURCES]
closure,missing=ns['imported_modules'](modules,mods)
assert not missing,missing
ident={os.path.relpath(modules[m],ROOT):H(modules[m])for m in sorted(closure)}
for p in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 ident[p]=H(ROOT/p)
r={'status':'running','scope':'Canonical actual codimension-three face Gaussian mass, normal point, incidence conormal and signed boundary coefficient from a selected exact tangent-facet presentation. No cardinality-three active-set assumption. Selection-to-all-incidences enumeration and global printed Green assembly are separate scopes.','release_wide_certification':False,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'initial_checkout_clean':False,'source_identity':ident,'target_count':6,'commands':[],'started_at_utc':now()}
def save():(OUT/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
def command(label,argv):
 p=OUT/(label+'.log');c={'label':label,'argv':argv,'cwd':str(ROOT),'started_at_utc':now(),'log':str(p.relative_to(ROOT))};r['commands'].append(c);save()
 with p.open('wb')as f:q=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
 c.update(exit_code=q.returncode,finished_at_utc=now(),log_sha256=H(p));save()
 if q.returncode:raise RuntimeError(label+' failed')
try:
 save();command('build',['lake','build','RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenCanonical'])
 for p in SOURCES:command('force-'+Path(p).stem,['lake','env','lean',p])
 command('types-and-axiom-audit',['lake','env','lean',str(OUT/'TypesAndAudit.lean')])
 x=json.loads((OUT/'types-and-axiom-audit.log').read_text());names=json.load(open(OUT/'targets.json'));assert{e['name']for e in x['endpoints']}==set(names)and len(x['endpoints'])==6;assert set(x['axiom_union'])<={'propext','Classical.choice','Quot.sound'}
 graph={e['name']:e['direct_project_dependencies']for e in x['project_dependency_graph']};assert all(set(v)<=set(graph)for v in graph.values())
 (OUT/'expanded-types.json').write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
 assert all(H(ROOT/p)==h for p,h in ident.items())
 r.update(status='passed',expanded_type_count=6,project_dependency_nodes=len(graph),axiom_union=x['axiom_union'],export_sha256=H(OUT/'expanded-types.json'),source_identity_after={p:H(ROOT/p)for p in ident},finished_at_utc=now());save()
except Exception as e:r.update(status='failed',failure=str(e),finished_at_utc=now());save();raise
print(json.dumps({'status':r['status'],'targets':6,'graph_nodes':r['project_dependency_nodes'],'sources':len(ident)}))

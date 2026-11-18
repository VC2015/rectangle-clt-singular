import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
PROJECT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent/'checkpoint-1'
MODULES=['SupplementalGCapIntegratedRemainder']
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
OUT.mkdir(exist_ok=False)
identity={f'RectangleCLTArxivV1/{m}.lean':sha(PROJECT/f'RectangleCLTArxivV1/{m}.lean') for m in MODULES}
names=[]
for name in identity:
 for n in re.findall(r'^(?:@\[[^\]]+\] )?theorem ([A-Za-z0-9_]+)',(PROJECT/name).read_text(),re.M):names.append('RectangleCLTArxivV1.'+n)
audit=OUT/'Audit.lean'; audit.write_text('import RectangleCLTArxivV1.SupplementalGCapIntegratedRemainder\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]\n  let targets := #['+',\n    '.join('``'+n for n in names)+']\n  for target in targets do\n    let axioms ← Lean.collectAxioms target\n    for ax in axioms do\n      unless allowed.contains ax do\n        throwError "Unexpected axiom {ax} in {target}"\n    logInfo m!"{target} uses {axioms.toList}"\n')

route_checks = [
 'RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound',
 'RectangleCLTArxivV1.intrinsic_seeded_fourth_remainder_bound',
 'RectangleCLTArxivV1.cap_abs_le_split_min',
 'RectangleCLTArxivV1.cap_integral_majorant_bound',
 'RectangleCLTArxivV1.cap_seededFourthRemainder_abs_intervalIntegrable',
 'RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase',
 'RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope']
with audit.open('a') as f:
 f.write('open Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.cap_seededFourthRemainder_bounded_integral_bound).run env).run {}\n')
 for dep in route_checks:
  f.write('  unless deps.visited.contains ``'+dep+' do\n    throwError "Missing actual proof step '+dep+'"\n')
 f.write('  if deps.visited.contains ``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_majorant then\n    throwError "Used normalized remainder rather than proving raw R4 bound"\n')
 f.write('  logInfo "PASS literal raw R4, actual time integrability, capped integral, and discharged concentration route"\n')
types=OUT/'Types.lean'; types.write_text('import RectangleCLTArxivV1.SupplementalGCapIntegratedRemainder\n'+''.join('#check @'+n+'\n' for n in names))
record={'scope':'Literal raw R4 absolute integral with dimension cap and actual envelope-derived relative moments, proved time integrability and actual concentration supplier discharged','source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'source_sha256':identity,'started_at_utc':now(),'status':'running','commands':[],'audit_targets':names,'actual_route_checks':route_checks}
(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
def run(label,argv):
 log=OUT/(label+'.log');row={'label':label,'argv':argv,'cwd':str(PROJECT),'started_at_utc':now(),'log':str(log.relative_to(PROJECT))};record['commands'].append(row);(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')
 with log.open('wb') as f:p=subprocess.run(argv,cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT)
 row.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(log));(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')
 if p.returncode:raise RuntimeError(label+' failed')
try:
 run('build',['lake','build','RectangleCLTArxivV1.SupplementalGCapIntegratedRemainder'])
 for m in MODULES:run('force-'+m,['lake','env','lean',f'RectangleCLTArxivV1/{m}.lean','-o',f'.lake/build/lib/lean/RectangleCLTArxivV1/{m}.olean'])
 run('audit',['lake','env','lean',str(audit.relative_to(PROJECT))])
 # Print the actual defining parameter structure from its archived namespace.
 text=types.read_text().replace('#print RectangleCLTArxivV1.SymmetricFamilyParameters','#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters');types.write_text(text)
 run('types',['lake','env','lean',str(types.relative_to(PROJECT))])
 expanded=OUT/'ExpandedTypes.lean';expanded.write_text((OUT.parent/'ExpandedTypes.template.lean').read_text())
 run('expanded-types',['lake','env','lean',str(expanded.relative_to(PROJECT))])
 raw=(OUT/'expanded-types.log').read_text();payload=json.loads(next(line for line in raw.splitlines() if line.startswith('{')));(OUT/'expanded-types.json').write_text(json.dumps(payload,indent=2)+'\n')
 record['expanded_types_sha256']=sha(OUT/'expanded-types.json')
 assert all(sha(PROJECT/p)==v for p,v in identity.items())
 record.update(status='passed',finished_at_utc=now(),audit_source_sha256=sha(audit),types_source_sha256=sha(types))
except Exception as e:record.update(status='failed',error=str(e),finished_at_utc=now());raise
finally:(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')

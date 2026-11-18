import datetime,hashlib,json,os,subprocess
from pathlib import Path
ROOT=Path.cwd();OUT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
x=json.loads((OUT/'expanded-types.json').read_text());names=[e['name'] for e in x['endpoints']]
checks={
'cap_seededFourthRemainder_rank_complementary_bound':['cap_posSemidef_minimal_factor','cap_covariance_rank_pos','cap_seededFourthRemainder_eq_patterns','cap_array_fourth_expectation_product_single_pair','cap_seeded_small_angle_pattern_bound','cap_seeded_pair_pattern_bound','cap_seeded_single_pattern_bound','capMatrix_translated_copy_bound_numeric','capThirdHermite_conditional_mass_bound_ae','capSecondHermite_conditional_mass_bound_ae','cap_seeded_pair_contribution_eq_second','cap_pair_geometric_mean','cap_seeded_pair_parallel_zero','capWhitenedCopy_quadratic_budget','cap_seeded_projection_hypotheses'],
'cap_seededFourthRemainder_rank_abs_intervalIntegrable':['cap_posSemidef_minimal_factor','cap_seededFourthRemainder_aestronglyMeasurable','cap_seededFourthRemainder_eq_measurable_expression','capSeededTestIntegral_measurable','capSeededTestIntegral_eq_seededLaw','cap_seededFourthRemainder_intervalIntegrable']}
audit=OUT/'Audit.lean';s='import RectangleCLTArxivV1.SupplementalGMinimalFactor\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n  let allowed := #[``propext,``Classical.choice,``Quot.sound]\n  let targets := #['+',\n    '.join('``'+n for n in names)+']\n  for target in targets do\n    let axs ← Lean.collectAxioms target\n    for ax in axs do\n      unless allowed.contains ax do\n        throwError "Unexpected axiom {ax} in {target}"\n    logInfo m!"{target} uses {axs.toList}"\n'
s+='open Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n'
for top,deps in checks.items():
 s+='  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.'+top+').run env).run {}\n'
 for dep in deps:s+='  unless deps.visited.contains ``RectangleCLTArxivV1.'+dep+' do\n    throwError "Missing actual proof step '+dep+'"\n'
 s+='  logInfo "PASS required actual route '+top+'"\n'
audit.write_text(s)
ledger=json.loads(Path('correspondence/supplemental-g-complementary-passages.json').read_text())
identity={}
for f in ledger['build_and_audit_receipts']+ledger['external_support_receipts']:
 r=json.loads(Path(f).read_text());assert str(r['status']).lower()=='pass' or r['status']=='passed',f
 if isinstance(r.get('source_sha256'),dict):identity.update(r['source_sha256'])
identity.update(ledger['source_sha256'])
for f,d in identity.items():assert sha(f)==d,(f,d)
record={'scope':'Independent full G3 endpoint types and strict43 proof-step audit plus required actual tensor/copy/seeded/pair/rank/time-measurability route assertions','status':'running','started_at_utc':now(),'source_sha256':identity,'audit_targets':names,'required_actual_routes':checks,'expanded_types_sha256':sha(OUT/'expanded-types.json')}
p=OUT/'run.json';p.write_text(json.dumps(record,indent=2)+'\n');env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
argv=['lake','env','lean',str(audit.relative_to(ROOT))]
with (OUT/'audit.log').open('wb') as f:r=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT,env=env,cwd=ROOT)
record.update(status='passed' if r.returncode==0 else 'failed',exit_code=r.returncode,argv=argv,finished_at_utc=now(),audit_source_sha256=sha(audit),audit_log_sha256=sha(OUT/'audit.log'))
for f,d in identity.items():assert sha(f)==d,(f,d)
p.write_text(json.dumps(record,indent=2)+'\n');raise SystemExit(r.returncode)

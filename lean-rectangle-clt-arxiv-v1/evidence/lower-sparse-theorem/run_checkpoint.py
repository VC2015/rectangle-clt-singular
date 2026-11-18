import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
PROJECT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent/'checkpoint-2'
MODULES=['LowerSparseWidthScales','LowerSparseWidthLimits','LowerSparseCalibration','LowerSparseUpperRate','LowerSparseTheorem']
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
OUT.mkdir(exist_ok=False)
identity={f'RectangleCLTArxivV1/{m}.lean':sha(PROJECT/f'RectangleCLTArxivV1/{m}.lean') for m in MODULES}
names=[]
for name in identity:
 for n in re.findall(r'^(?:@\[[^\]]+\] )?theorem ([A-Za-z0-9_]+)',(PROJECT/name).read_text(),re.M):names.append('RectangleCLTArxivV1.'+n)
audit=OUT/'Audit.lean'; audit.write_text('import RectangleCLTArxivV1.LowerSparseTheorem\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]\n  let targets := #['+',\n    '.join('``'+n for n in names)+']\n  for target in targets do\n    let axioms ← Lean.collectAxioms target\n    for ax in axioms do\n      unless allowed.contains ax do\n        throwError "Unexpected axiom {ax} in {target}"\n    logInfo m!"{target} uses {axioms.toList}"\n')
audit.write_text(audit.read_text()+'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_lower,
    ``RectangleCLTArxivV1.theorem_8_sparse_polynomial_moment_two_sided]
  let action : CollectAxioms.M Unit := targets.forM CollectAxioms.collect
  let (_,deps) := (action.run env).run {}
  let blocked := #["RectangleCLT.Companion.SplitV4.sparseFamilyCalibration",
    "RectangleCLT.Companion.SplitV4.sparsePaperCalibration",
    "RectangleCLT.Companion.SplitV4.eventually_sparseFamily_parameters",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLowerScale_of_paperRate",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLowerTheta",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLowerVariance",
    "RectangleCLT.Companion.SplitV4.tendsto_sparseLower_scale_bounded_ratio"]
  for n in deps.visited.toList do
    if blocked.contains n.toString then
      throwError "Forbidden old worst-dimension scale-small route {n}"
  let required := #[``RectangleCLTArxivV1.lowerSparseCalibration_of_scalar_limits,
    ``RectangleCLTArxivV1.tendsto_lowerSparseRawWidth,
    ``RectangleCLTArxivV1.tendsto_lowerSparseTheta,
    ``RectangleCLTArxivV1.tendsto_lowerSparseVariance,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEffectiveAmplitude,
    ``RectangleCLTArxivV1.exists_lowerFamily_masked_width_detection_constant,
    ``RectangleCLTArxivV1.eventually_lowerSparse_membership,
    ``RectangleCLTArxivV1.theorem_2_ii_intrinsic]
  for n in required do
    unless deps.visited.contains n do
      throwError "Sparse final proof route omits required checked declaration {n}"
  logInfo m!"Checked sparse final proof route through {deps.visited.size} constants: no forbidden old scale-small route; every required actual-law, weak-width and matching-upper component present."
''')
types=OUT/'Types.lean'; types.write_text('import RectangleCLTArxivV1.LowerSparseTheorem\n#print RectangleCLTArxivV1.SymmetricFamilyParameters\n'+''.join('#check @'+n+'\n' for n in names))
record={'scope':'Theorem 8 actual sparse polynomial moment construction and matching two-sided rate under the exact width-sensitive sparse headline regime; actual iid symmetric Cq observations, prescribed width, signed detecting orthant, no old worst-dimension scale-small calibration','source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'source_sha256':identity,'started_at_utc':now(),'status':'running','commands':[],'audit_targets':names}
(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
def run(label,argv):
 log=OUT/(label+'.log');row={'label':label,'argv':argv,'cwd':str(PROJECT),'started_at_utc':now(),'log':str(log.relative_to(PROJECT))};record['commands'].append(row);(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')
 with log.open('wb') as f:p=subprocess.run(argv,cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT)
 row.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(log));(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')
 if p.returncode:raise RuntimeError(label+' failed')
try:
 run('build',['lake','build','RectangleCLTArxivV1.LowerSparseTheorem'])
 for m in MODULES:run('force-'+m,['lake','env','lean',f'RectangleCLTArxivV1/{m}.lean','-o',f'.lake/build/lib/lean/RectangleCLTArxivV1/{m}.olean'])
 run('audit',['lake','env','lean',str(audit.relative_to(PROJECT))])
 # Print the actual defining parameter structure from its archived namespace.
 text=types.read_text().replace('#print RectangleCLTArxivV1.SymmetricFamilyParameters','#print RectangleCLT.Companion.SplitV4.SymmetricFamilyParameters');types.write_text(text)
 run('types',['lake','env','lean',str(types.relative_to(PROJECT))])
 assert all(sha(PROJECT/p)==v for p,v in identity.items())
 record.update(status='passed',finished_at_utc=now(),audit_source_sha256=sha(audit),types_source_sha256=sha(types))
except Exception as e:record.update(status='failed',error=str(e),finished_at_utc=now());raise
finally:(OUT/'run.json').write_text(json.dumps(record,indent=2)+'\n')

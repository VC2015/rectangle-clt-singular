#!/usr/bin/env python3
"""Force-check and strictly audit the actual affine Gaussian-section Green identity."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,re
P=Path(__file__).resolve().parents[3]
E=P/'evidence/supplemental-h-positive-first/checkpoint-1'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=set()
mods=['SupplementalHWeightedGammaPrimitive', 'PositiveFirstCoarea', 'PositiveFirstCoareaBounds', 'PositiveFirstCoareaDerivative', 'PositiveGammaFirstCoarea']
queue=[P/('RectangleCLTArxivV1/'+m+'.lean') for m in mods]
while queue:
    path=queue.pop()
    if path in paths:continue
    paths.add(path)
    queue.extend(P/(n.replace('.','/')+'.lean') for n in re.findall(r'^import (RectangleCLTArxivV1(?:\.[A-Za-z0-9_]+)*)',path.read_text(),re.M))
paths.update(E/n for n in ['Audit.lean','Types.lean','targets.json','run_checkpoint.py'])
paths.update(P/n for n in ['lakefile.toml','lake-manifest.json','lean-toolchain','source-pins.json'])
identity=lambda:{str(p.relative_to(P)):sha(p) for p in sorted(paths)}
initial=identity()
(E/'source-freeze.json').write_text(json.dumps({'created_at':now(),'sha256':initial},indent=2)+'\n')
record={'scope':'Actual positive first mass and actual pair-plane Gaussian tests, true weighted Gamma mixture Fubini, exact first normal section, genuine integrability and continuity, local first coarea and volume-AE derivative, global first primitive bounds and Lipschitz, exact positive first soft/Gamma coarea with all analytic premises discharged. No full-family independence.',
'release_wide_certification':False,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),
'started_at_utc':now(),'source_sha256':initial,'endpoints':json.loads((E/'targets.json').read_text()),'commands':[],'status':'running'}
def save():(E/'run.json').write_text(json.dumps(record,indent=2)+'\n')
def run(label,argv):
    log=E/(label+'.log')
    row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str(log.relative_to(P))}
    record['commands'].append(row);save()
    with log.open('wb') as out: result=subprocess.run(argv,cwd=P,env=os.environ.copy(),stdout=out,stderr=subprocess.STDOUT)
    row.update(exit_code=result.returncode,finished_at_utc=now(),log_sha256=sha(log));save()
    if result.returncode:raise RuntimeError(label+' failed')
save()
try:
    run('build',['lake','build']+['RectangleCLTArxivV1.'+m for m in mods])
    for m in mods:
        run('force-'+m,['lake','env','lean','RectangleCLTArxivV1/'+m+'.lean','-o','.lake/build/lib/lean/RectangleCLTArxivV1/'+m+'.olean'])
    run('audit',['lake','env','lean','evidence/supplemental-h-positive-first/checkpoint-1/Audit.lean'])
    run('types-dependencies',['lake','env','lean','evidence/supplemental-h-positive-first/checkpoint-1/Types.lean'])
    parsed=json.loads((E/'types-dependencies.log').read_text())
    record.update(expanded_types=len(parsed['endpoints']),project_dependency_nodes=len(parsed['project_dependency_graph']))
    assert initial==identity(),'Proof sources changed during this checkpoint'
    record.update(status='passed',finished_at_utc=now(),final_source_sha256=identity());save()
except BaseException as e:
    record.update(status='failed',finished_at_utc=now(),error=str(e));save();raise

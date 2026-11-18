#!/usr/bin/env python3
"""Force-check and strictly audit the actual H.1 weighted ridge cancellation."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,re
P=Path(__file__).resolve().parents[2]
E=P/'evidence/supplemental-h-surface-geometry'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=set()
queue=[P/'RectangleCLTArxivV1/SupplementalHSurfaceGeometry.lean']
while queue:
    path=queue.pop()
    if path in paths:continue
    paths.add(path)
    queue.extend(P/(n.replace('.','/')+'.lean') for n in re.findall(r'^import (RectangleCLTArxivV1(?:\.[A-Za-z0-9_]+)*)',path.read_text(),re.M))
paths.update(E/n for n in ['Audit.lean','targets.json','run_checkpoint.py'])
paths.update(P/n for n in ['lakefile.toml','lake-manifest.json','lean-toolchain','source-pins.json'])
identity=lambda:{str(p.relative_to(P)):sha(p) for p in sorted(paths)}
initial=identity()
record={'scope':'Supplemental H.1 weighted ridge cancellation with actual conormals, angle and constructed projection radius; not the Hausdorff surface comparison',
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
    run('build',['lake','build','RectangleCLTArxivV1.SupplementalHSurfaceGeometry'])
    run('force-source',['lake','env','lean','RectangleCLTArxivV1/SupplementalHSurfaceGeometry.lean','-o','.lake/build/lib/lean/RectangleCLTArxivV1/SupplementalHSurfaceGeometry.olean'])
    run('audit',['lake','env','lean','evidence/supplemental-h-surface-geometry/Audit.lean'])
    assert initial==identity(),'Proof sources changed during this checkpoint'
    record.update(status='passed',finished_at_utc=now(),final_source_sha256=identity());save()
except BaseException as e:
    record.update(status='failed',finished_at_utc=now(),error=str(e));save();raise

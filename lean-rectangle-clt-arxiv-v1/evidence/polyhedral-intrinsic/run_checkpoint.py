#!/usr/bin/env python3
"""Build, force, expand and strictly audit the actual Corollary 3 transfer."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,re,sys
P=Path(__file__).resolve().parents[2]
E=P/'evidence/polyhedral-intrinsic'
O=E/(sys.argv[1] if len(sys.argv)>1 else 'checkpoint-2')
O.mkdir(parents=True,exist_ok=True)
MODULES=['PolyhedralIntrinsicInputs','PolyhedralIntrinsicZeroFaces','PolyhedralIntrinsicBounded','PolyhedralIntrinsicPolynomial','PolyhedralIntrinsicSubexponential','PolyhedralIntrinsicSubexponentialAllFaces','PolyhedralIntrinsicMain']
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=set()
queue=[P/'RectangleCLTArxivV1/PolyhedralIntrinsicMain.lean']
while queue:
    path=queue.pop()
    if path in paths:continue
    paths.add(path)
    queue.extend(P/(n.replace('.','/')+'.lean') for n in re.findall(r'^import (RectangleCLTArxivV1(?:\.[A-Za-z0-9_]+)*)',path.read_text(),re.M))
paths.update(E/n for n in ['Audit.lean','ExpandedTypes.lean','targets.json','run_checkpoint.py'])
paths.update(P/n for n in ['lakefile.toml','lake-manifest.json','lean-toolchain','source-pins.json'])
identity=lambda:{str(p.relative_to(P)):sha(p) for p in sorted(paths)}
initial=identity()
(O/'source-freeze.json').write_text(json.dumps({'frozen_at_utc':now(),'source_sha256':initial},indent=2)+'\n')
record={'scope':'Corollary3 / AppendixD.2 intrinsic polyhedral transfer: both bounded rates, both polynomial branches, exact Orlicz scale, canonical zero-face selection and actual Gaussian width',
'release_wide_certification':False,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),
'started_at_utc':now(),'source_sha256':initial,'endpoints':json.loads((E/'targets.json').read_text()),'commands':[],'status':'running'}
def save():(O/'run.json').write_text(json.dumps(record,indent=2)+'\n')
def run(label,argv):
    log=O/(label+'.log')
    row={'label':label,'argv':argv,'cwd':str(P),'started_at_utc':now(),'log':str(log.relative_to(P))}
    record['commands'].append(row);save()
    with log.open('wb') as out: result=subprocess.run(argv,cwd=P,env=os.environ.copy(),stdout=out,stderr=subprocess.STDOUT)
    row.update(exit_code=result.returncode,finished_at_utc=now(),log_sha256=sha(log));save()
    if result.returncode:raise RuntimeError(label+' failed')
    return log
save()
try:
    run('build',['lake','build','RectangleCLTArxivV1.PolyhedralIntrinsicMain'])
    for name in MODULES:
        run('force-'+name,['lake','env','lean','RectangleCLTArxivV1/'+name+'.lean','-o','.lake/build/lib/lean/RectangleCLTArxivV1/'+name+'.olean'])
    run('audit',['lake','env','lean','evidence/polyhedral-intrinsic/Audit.lean'])
    log=run('expanded-types',['lake','env','lean','evidence/polyhedral-intrinsic/ExpandedTypes.lean'])
    data=json.loads(log.read_text());nodes={row['name'] for row in data['project_dependency_graph']}
    forbidden=['RectangleCLT.Companion.SplitV4.boundedPolyhedralEnvelopeCLT','RectangleCLT.Companion.SplitV4.relativePolyhedralCLT','RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT','RectangleCLT.Companion.SplitV4.orliczPolyhedralCLT']
    assert not nodes.intersection(forbidden),'Archived terminal polyhedral CLT was used'
    required=['RectangleCLTArxivV1.intrinsicFourthMomentCLT_of_quadratic_bounds','RectangleCLTArxivV1.intrinsicEnvelopeCLT','RectangleCLTArxivV1.theorem_2_intrinsic','RectangleCLTArxivV1.subexponentialCLT_intrinsic']
    assert all(n in nodes for n in required),'Missing new intrinsic supplier'
    record['dependency_check']={'project_nodes':len(nodes),'forbidden_archival_polyhedral_endpoints_present':[],'required_new_intrinsic_suppliers':required}
    assert initial==identity(),'Proof sources changed during this checkpoint'
    record.update(status='passed',finished_at_utc=now(),final_source_sha256=identity());save()
except BaseException as e:
    record.update(status='failed',finished_at_utc=now(),error=str(e));save();raise

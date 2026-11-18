import datetime,hashlib,json,os,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent/'checkpoint-1'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
mods=['IntrinsicBoundedConcentration','BoundedRectangleIntrinsic','IntrinsicGaussianBoundary','GaussianC1Statement','GaussianRectangleIntrinsic','ConcentrationLemma','ThinnedMaximum','SeededIntrinsicConcentration','NormalizedObservationsIntrinsic','SmoothingIntrinsic','SmoothingError']
archive=['Printed/BoundedConcentration','CubeCopySelection','IntrinsicVariance','CubeContraction','IntrinsicGaussianBoundary','GaussianMaximumLimits','Printed/GaussianMollification','Printed/ClockTails','Printed/ClockMean','Printed/EndpointMixture']
source=[f'RectangleCLTArxivV1/{m}.lean' for m in mods]+['../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/'+m+'.lean' for m in archive]
# Archive regularity and support modules whose exact proof types are also mapped.
for m in ['GaussianIntrinsicConcentration','GaussianMaximumMGF','ObservationNormalization']:
 p='../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/'+m+'.lean'
 if Path(ROOT/p).exists():source.append(p)
identity={p:sha(ROOT/p) for p in source};targets=json.loads((OUT.parent/'targets.json').read_text())
r={'scope':'Fresh selected-source build, force and strict full-type/dependency correspondence for C1 bounded/Gaussian, actual Corollary1 normalization and Lemma2 endpoint mixture/clock proof. No q0 derivative correspondence or release-wide claim.','release_wide_certification':False,'status':'running','started_at_utc':now(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'source_sha256':identity,'strict_targets':targets,'commands':[]};rec=OUT/'run.json';rec.write_text(json.dumps(r,indent=2)+'\n')
env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
def run(label,argv):
 row={'label':label,'argv':argv,'started_at_utc':now(),'log':str((OUT/(label+'.log')).relative_to(ROOT))};r['commands'].append(row);rec.write_text(json.dumps(r,indent=2)+'\n')
 with (ROOT/row['log']).open('wb') as f:p=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
 row.update(exit_code=p.returncode,finished_at_utc=now(),log_sha256=sha(ROOT/row['log']));rec.write_text(json.dumps(r,indent=2)+'\n')
 if p.returncode:raise RuntimeError(label+' failed')
try:
 run('build',['lake','build','RectangleCLTArxivV1.ConcentrationLemma','RectangleCLTArxivV1.SeededIntrinsicConcentration','RectangleCLTArxivV1.NormalizedObservationsIntrinsic','RectangleCLTArxivV1.SmoothingError'])
 for m in mods:run('force-'+m,['lake','env','lean',f'RectangleCLTArxivV1/{m}.lean'])
 for m in archive:run('force-archive-'+m.replace('/','-'),['lake','env','lean','../lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/'+m+'.lean'])
 run('types-and-strict-audit',['lake','env','lean',str((OUT/'TypesAndAudit.lean').relative_to(ROOT))])
 raw=(OUT/'types-and-strict-audit.log').read_text();x=json.loads(next(l for l in raw.splitlines() if l.startswith('{')));(OUT/'expanded-types.json').write_text(json.dumps(x,indent=2)+'\n');r['full_type_count']=len(x['endpoints']);r['dependency_nodes']=len(x['project_dependency_graph']);r['expanded_types_sha256']=sha(OUT/'expanded-types.json')
 for p,d in identity.items():assert sha(ROOT/p)==d,p
 r.update(status='passed',finished_at_utc=now())
except Exception as e:r.update(status='failed',error=str(e),finished_at_utc=now());raise
finally:rec.write_text(json.dumps(r,indent=2)+'\n')

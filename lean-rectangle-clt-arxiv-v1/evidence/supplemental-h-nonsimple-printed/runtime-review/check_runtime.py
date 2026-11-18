"""Read-only independent runtime verification; writes only its final review.

This script does not run Lean, Lake, cache preparation or acceptance tooling.
It refuses to certify a running or failed receipt.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
LIVE = Path(__file__).resolve().parents[3]
CLEAN = Path('/workspace/rectangle-clt-h1-printed-clean/lean-rectangle-clt-arxiv-v1')
OUT = LIVE / 'evidence/supplemental-h-nonsimple-printed'
CP = OUT / 'clean-checkpoint'
FINAL = OUT / 'clean-independent-archive-review.json'
BASE = '443fbc667ed3c3ee47369e028c2c4280a5eed604'
COMMIT = '63c975b7bd2176ddf559dbed1b2e087e191f7a45'
BASE_SHA = '3500c2efdb929397434a7e2201f0b203b51b14bd362d53e78666be40afb62ba5'
HELD = {'tools/prepare_h1_verified_native_cache.py':'d304a1b22a416464d530a8dc4cf243bb336592da3c07b14da6a6fc864336404f',
        'tools/run_h1_printed_clean_checkpoint.py':'0c4fd42389f037c7941d223e71efd6d6cb4c7c779373fac9215b9cc62576e345'}
def H(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p): return json.loads(Path(p).read_text())
def G(p,*a): return subprocess.check_output(['git',*a],cwd=p,text=True).strip()
def require(x,msg):
    if not x: raise RuntimeError(msg)
def declarations(path):
    stack=[];result=[]
    for raw in path.read_text().splitlines():
        line=raw.strip();n=re.match(r'namespace\s+([\w.]+)',line)
        if n: stack.append(('ns',n.group(1)));continue
        if re.match(r'(?:noncomputable\s+)?section(?:\s|$)',line):stack.append(('section',''));continue
        if re.match(r'end(?:\s+[\w.]+)?\s*$',line):
            if stack:stack.pop()
            continue
        line=re.sub(r'^@\[[^]]*\]\s*','',line)
        n=re.match(r'(?:(private|protected)\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|structure|class|inductive|abbrev|opaque|axiom|instance)\s+([\w.\']+)',line)
        if n and n.group(1)!='private':
            ns='.'.join(v for k,v in stack if k=='ns');name=(ns+'.' if ns else '')+n.group(2)
            if name.startswith(('RectangleCLT','GenericChaining','Kane')):result.append(name)
    return result
r=J(CP/'run.json'); initial_receipt_sha=H(CP/'run.json')
require(r['status']=='passed','Receipt has not passed; no review written')
require(not FINAL.exists(),'Refusing to overwrite a completed independent review')
require(r['source_commit']==COMMIT and G(CLEAN,'rev-parse','HEAD')==COMMIT,'Proof commit')
require(G(CLEAN,'rev-parse','HEAD^{tree}')==r['source_tree'],'Proof tree')
require(not r['initial_git_status'] and not G(CLEAN,'status','--porcelain'),'Clean proof checkout')
require(r['historical_1949_target_mapping_replayed'] is False and r['release_wide_certification'] is False,'Honest delta scope')
for p,h in HELD.items():require(H(CLEAN/p)==h,'Held tool '+p)
require(r['source_identity']==r['final_source_identity'],'Before/after identities')
for p,h in r['source_identity'].items():require(H(CLEAN/p)==h,'Source/harness byte drift '+p)
require(H(CP/'NewTypesAndAudit.lean')==r['harness_sha256'],'Generated harness digest')
require('set_option pp.all true' in (CP/'NewTypesAndAudit.lean').read_text(),'Full pp.all harness')
basepath=CLEAN/'evidence/final-clean-checkpoint/run.json';require(H(basepath)==BASE_SHA,'Sealed baseline receipt');base=J(basepath)
require(base['status']=='passed' and base['source_commit']==BASE==r['baseline_source_commit'],'Sealed baseline commit')
old=base['final_source_identity']['files']
natives={str(p.relative_to(CLEAN)):H(p)for p in sorted((CLEAN/'RectangleCLTArxivV1').rglob('*.lean'))}
unchanged={p:h for p,h in natives.items()if old.get(p)==h};delta={p:h for p,h in natives.items()if old.get(p)!=h}
require(unchanged==r['unchanged_baseline_native_sources'] and delta==r['new_or_changed_native_sources'],'Native partition')
require(len(unchanged)==417 and len(delta)==66,'Expected exact runtime native counts')
oldtree=set(G(CLEAN.parent,'ls-tree','-r','--name-only',BASE,'--',CLEAN.name+'/RectangleCLTArxivV1').splitlines())
preexisting=[p for p in delta if CLEAN.name+'/'+p in oldtree];newfiles=[p for p in delta if p not in preexisting]
require(len(preexisting)==4 and len(newfiles)==62,'New versus previously unbound sources')
for p in preexisting:
    oldbytes=subprocess.check_output(['git','show',BASE+':'+CLEAN.name+'/'+p],cwd=CLEAN.parent)
    require(hashlib.sha256(oldbytes).hexdigest()==delta[p],'Old unbound source changed '+p)
cache=r['cache_preparation'];np=Path(cache['native_receipt']);dp=Path(cache['dependency_receipt'])
require(H(np)==cache['native_receipt_sha256'] and H(dp)==cache['dependency_receipt_sha256'],'Cache receipt pins')
nc=J(np);dc=J(dp)
require(nc['proof_check']is False and nc['baseline_commit']==BASE and nc['baseline_receipt_sha256']==BASE_SHA,'Native cache baseline')
require(nc['new_native_artifacts_copied']is False and nc['root_artifact_copied']is False,'No new or Root copied')
require(Path(nc['destination_checkout']).resolve()==CLEAN.parent.resolve(),'Native cache destination')
origin=Path(nc['source_checkout'])/CLEAN.name
require(G(origin,'rev-parse','HEAD')==BASE and not G(origin,'status','--porcelain'),'Old clean cache origin')
reusable={q['source']:q['sha256']for q in nc['source_identical_native_modules']}
require(reusable==unchanged and len(nc['source_identical_native_modules'])==417,'Exact unique old cache seeds')
for p,h in reusable.items():require(H(origin/p)==h==old[p]==H(CLEAN/p),'Byte-identical native source '+p)
artifact_paths=[]
for q in nc['artifacts']:
    p=q['source'];require(p in reusable and q['source_sha256']==reusable[p],'Native artifact source')
    m=str(Path(p).with_suffix(''));allowed={'.lake/build/lib/lean/'+m+s for s in ['.olean','.olean.hash','.ilean','.ilean.hash','.trace']}
    allowed|={'.lake/build/ir/'+m+s for s in ['.c','.c.hash']}
    require(q['path']in allowed,'Native artifact allowlist');artifact_paths.append(q['path'])
    require(H(origin/q['path'])==q['sha256'],'Old-origin artifact digest '+q['path'])
require(len(set(artifact_paths))==len(artifact_paths)==2919,'Unique native artifact inventory')
for p in reusable:
    m=str(Path(p).with_suffix(''));require(all('.lake/build/lib/lean/'+m+s in artifact_paths for s in ['.olean','.olean.hash']),'Required native cache artifacts')
require(dc['proof_check']is False and dc['new_c2_build_artifacts_copied']is False,'Dependency cache scope')
require(Path(dc['destination_checkout']).resolve()==CLEAN.parent.resolve(),'Dependency cache destination')
archive_sources={}
for q in dc['artifacts']:
    p=q['source_path'];require(Path(p).parts[0]in ['lean-kane','lean-rectangle-clt-local','lean-rectangle-clt-singular'],'Archive-only cache')
    require(q['path'].startswith(Path(p).parts[0]+'/.lake/build/'),'Archive artifact prefix')
    require(H(CLEAN.parent/p)==q['source_sha256'],'Archive source at destination')
    require(H(Path(dc['source_checkout'])/p)==q['source_sha256'],'Archive source at origin')
    archive_sources[p]=q['source_sha256']
require(len(archive_sources)==dc['source_identical_modules']==959,'Archive cache source count')
commands=r['commands'];logs={}
for q in commands:
    require(q.get('exit_code')==0,'Command did not exit zero '+q['label']);p=CP/q['log']
    require(p.is_file() and H(p)==q['log_sha256'],'Command log hash '+q['label'])
    require(Path(q['cwd']).resolve()==CLEAN.resolve(),'Command cwd')
    require(q['label']not in logs,'Duplicate command label');logs[q['label']]=p
forces=[q for q in commands if q['label'].startswith('force-')and q['label']!='force-root']
forcepaths=[q['argv'][3]for q in forces];require(len(forcepaths)==len(set(forcepaths))==66 and set(forcepaths)==set(delta),'Direct-force source bijection')
ordered=r['forced_modules'];require([q['argv'][3][:-5].replace('/','.')for q in forces]==ordered,'Force order receipt')
positions={m:i for i,m in enumerate(ordered)}
for m in ordered:
    for dep in re.findall(r'^import\s+([\w.]+)',(CLEAN/(m.replace('.','/')+'.lean')).read_text(),re.M):
        if dep in positions:require(positions[dep]<positions[m],'Topological force order')
require(next(q for q in commands if q['label']=='library-and-extension-build')['argv']==['lake','build','RectangleCLTArxivV1']+ordered,'Entire library build argv')
require('Build completed successfully.'in logs['library-and-extension-build'].read_text(),'Successful library build')
require(next(q for q in commands if q['label']=='force-root')['argv'][3]=='RectangleCLTArxivV1.lean','Root direct replay')
version=(CLEAN/'lean-toolchain').read_text().strip().rsplit(':v',1)[-1]
require(re.search(r'\bversion\s+'+re.escape(version)+r'[,)]',logs['lean-version'].read_text()),'Lean toolchain match')
pins=J(CP/'pins.json');require(pins['passed']is True and all(q['passed']for q in pins['checks']),'Source/dependency pins')
manifest=J(CLEAN/'lake-manifest.json');expected={q['name']:q['rev']for q in manifest['packages']if q['type']=='git'}
require(set(expected)==set(r['git_dependencies']),'Every Git package bound')
for name,rev in expected.items():
    q=r['git_dependencies'][name];p=CLEAN/q['path'];require(q['expected_commit']==q['actual_commit']==rev,'Package receipt revision')
    require(G(p,'rev-parse','HEAD')==rev and not G(p,'status','--porcelain','--untracked-files=no'),'Pinned clean Git package '+name)
new=J(logs['new-full-types-and-axiom-audit']);targets=r['new_public_targets'];require(len(targets)==len(set(targets))==537,'Explicit target inventory')
providers={}
for p in delta:
    for n in declarations(CLEAN/p):
        require(n not in providers,'Duplicate independent textual provider '+n);providers[n]=p[:-5].replace('/','.')
require(set(providers)==set(targets),'Independent explicit-declaration coverage')
require(len(new['endpoints'])==537 and {q['name']for q in new['endpoints']}==set(targets),'Exact new full types')
require(all(q['expanded_type']and q['kernel_import_module']==providers[q['name']]for q in new['endpoints']),'Actual new providers and nonempty types')
allowed={'propext','Classical.choice','Quot.sound'};require(set(new['axiom_union'])==allowed,'New complete axiom union')
graph={q['name']:set(q['direct_project_dependencies'])for q in new['project_dependency_graph']}
require(set(targets)<=graph.keys()and all(v<=graph.keys()for v in graph.values()),'Closed new kernel graph')
registered=J(logs['registered-types-and-dependencies']);require(all(q['expanded_type'] for q in registered['endpoints']),'Registered nonempty full types');rg={q['name']:set(q['direct_project_dependencies'])for q in registered['project_dependency_graph']}
require(all(v<=rg.keys()for v in rg.values()),'Registered graph closure')
dep_source=(CLEAN/'Correspondence/Dependencies.lean').read_text()
require('targets.forM Lean.CollectAxioms.collect' in dep_source and 'unless forbidden.isEmpty do throwError' in dep_source and all(n in dep_source for n in ['``propext','``Classical.choice','``Quot.sound']),'Executed registered dependency axiom guard')
audittext=(CLEAN/'Audit.lean').read_text().split('let targets := #[',1)[1].split(']',1)[0]
auditnames=re.findall(r'``([\w.\']+)',audittext)
depnames={q['name'] for q in registered['endpoints']}
archive_extra={'RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent','RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf'}
require(len(auditnames)==len(set(auditnames))==182 and len(depnames)==184 and set(auditnames)<=depnames and depnames-set(auditnames)==archive_extra,'Registered Audit/types intentional two-provider difference')
require(logs['registered-axiom-audit'].read_text().count('(shared transitive axiom audit)')==len(auditnames)==r['registered_axiom_audit_targets'],'Registered actual audit count')
queue=['RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_Green_actualFaces'];route=set()
while queue:
    n=queue.pop()
    if n in route:continue
    route.add(n);queue+=list(graph[n])
required=['hardGaussianSignedRidgeTerm_Green_actualFace','ActualRidgeFacetPresentation.selectedActualFaceEquiv','ActualRidgeFacetPresentation.boundaryCoefficient_eq_actualIncidence','gaussianFrameHardMass_eq_actualFaceMass','hardGaussianRidgeLeadingTerm_eq_actualFace','half_native_pair_sum_eq_actual_ridge_sum','nonsimpleActualThirdBoundary_eq_ridge_incidence_sum']
require({'RectangleCLTArxivV1.'+n for n in required}<=route,'Actual nonsimple geometric route')
forbidden={'RectangleCLTArxivV1.'+n for n in ['ae_hardGaussianWeightedRidgeIntegral_Green','integrable_abs_bound_of_ae_parameter_continuity','actualFacet_weightedRidgeIntegral_concentrated_base','ae_localizedGaussianSurfaceEstimates']}
require(not route&forbidden,'No Fatou/AE final Green bypass')
require(H(CP/'run.json')==initial_receipt_sha,'Receipt changed during independent review')
require(not G(CLEAN,'status','--porcelain') and G(CLEAN,'rev-parse','HEAD')==COMMIT,'Final independent clean check')
review={'status':'passed','scope':'Independent read-only runtime review of the clean H1 printed nonsimple delta checkpoint; no additional Lean and no rerun of the historical 1949 manuscript mapping.','reviewer':'archive_h_resume','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'receipt':str((CP/'run.json').relative_to(LIVE)),'receipt_sha256':H(CP/'run.json'),'proof_checkout':str(CLEAN.parent),'proof_commit':COMMIT,'proof_tree':r['source_tree'],'held_tool_identity':HELD,'source_and_harness_identity':r['final_source_identity'],'generated_harness_sha256':r['harness_sha256'],'command_log_identity':{q['log']:q['log_sha256']for q in commands},'command_count':len(commands),'new_or_newly_replayed_native_modules':66,'truly_new_native_files':newfiles,'preexisting_unbound_replayed_native_files':preexisting,'unchanged_native_cache_modules':417,'unchanged_native_cache_artifacts':2919,'archive_dependency_cache_modules':959,'native_cache_receipt_sha256':H(np),'dependency_cache_receipt_sha256':H(dp),'new_explicit_public_targets':537,'new_full_type_export_sha256':H(logs['new-full-types-and-axiom-audit']),'new_closed_project_graph_nodes':len(graph),'new_axiom_union':new['axiom_union'],'registered_explicit_type_count':len(registered['endpoints']),'registered_closed_project_graph_nodes':len(rg),'registered_type_export_sha256':H(logs['registered-types-and-dependencies']),'registered_audit_targets':len(auditnames),'registered_extra_archive_provider_types':sorted(archive_extra),'pointwise_green_route_nodes':len(route),'pointwise_green_required_routes':required,'forbidden_Fatou_AE_routes_found':sorted(route&forbidden),'pins_report_sha256':H(CP/'pins.json'),'git_dependencies':r['git_dependencies'],'independent_checker':str(Path(__file__).relative_to(LIVE)),'independent_checker_sha256':H(__file__),'findings':[],'checks':['All completed commands exit zero and every exact log hash is verified.','Exact source identities, commit/tree and Git dependency revisions/clean states are verified.','Native cache seeds are 417 byte-identical sealed-baseline modules; no new or Root cache artifact appears.','All 66 replayed modules have one correctly ordered direct source elaboration;62 are new files and 4 existed but were absent from the old baseline native set.','All 537 explicit source declarations are independently harvested, matched to exported kernel provider/full type, and audited by a complete standard-three axiom union.','Registered Audit has 182 targets; the 184 registered full types add exactly two explicitly disclosed archival provider types. Both full kernel dependency graphs close.','The actual pointwise Green route reaches exact actual mass, selected-face bijection, pair count and signed regrouping; the old Fatou/AE headline route is absent.'],'limits':['This is the delta checkpoint plus current registered audit. The old 1949 manuscript-mapping receipt is historical and was not rerun.','Cache preparation is not a fresh proof check of unchanged old modules.','Raw unnormalized Hausdorff measure normalization is outside this runtime review.']}
FINAL.write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps({'status':'passed','review':str(FINAL),'sha256':H(FINAL),'commands':len(commands),'new_targets':537,'new_graph':len(graph),'registered':len(auditnames)}))

#!/usr/bin/env python3
"""Prepare and run exact multi-ledger mapping in a separately frozen clean checkout.

Planning is read-only. Execution never edits the library root or Audit.lean.
The axiom check uses one shared complete kernel traversal over every target.
"""
import argparse,collections,datetime,hashlib,json,os,re,subprocess
from pathlib import Path

PROJECT_PREFIXES=('RectangleCLTArxivV1','RectangleCLTCompanion','RectangleCLT','GenericChaining','Kane')
NAME=re.compile(r"(?:_private\.)?(?:RectangleCLT(?:ArxivV1)?|GenericChaining|Kane)(?:\.[\w']+)+$")
NAME_KEYS={'new_declarations','new_declaration_candidates','new_declaration','lean_declarations','lean_endpoints','mapped_declarations','checked_declarations','support_declarations','archived_declaration_candidates','audited_dependency_candidates','declarations','theorems','final_theorems','headline_theorems','public_declarations','public_endpoints','strict_checked_declarations','endpoints','endpoint','declaration','name','public','internal','exact_public_endpoint','auxiliary_unrescaled_public_endpoint','checked_obstruction_endpoint','checked_final_endpoint','minimal_rank_constructor'}
SKIP={'project_dependency_graph','direct_dependencies','direct_project_dependencies','transitive_dependencies','transitive_project_dependencies','kernel_transitive_dependencies','dependency_graph','dependency_bindings','dependency_evidence','source_identity','source_files','sources','reviewed_source_sha256','core_source_sha256','source_sha256','source_ownership','source_snapshot','required_actual_routes','forbidden_dependencies','forbidden_target_bound_dependencies','excluded_dependencies','historical_candidates','archive_inputs','archive_candidate','module','imports'}
DEFAULT_EXCLUSIONS={'correspondence/lower-width-passages.json':'Historical early Gaussian support draft; superseded by actual F1–F6/lower-headline ledgers. Its open headline notes are preserved, not accepted mappings.'}
NON_DECLARATION_NOTES={('c2-passages.json','/passages/1/audited_dependency_candidates/0'):
 'Scalar Bernstein MGF implementation and Chernoff optimization in the archive; exact expanded type and new instantiation pending.'}
NOTE_SUPERSESSION_ENDPOINTS=[
 'RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf',
 'RectangleCLTArxivV1.bounded_sum_abs_tail',
 'RectangleCLTArxivV1.signedProcess_hasMixedTail']

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def put(p,d):Path(p).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def git(root,*args):return subprocess.check_output(['git',*args],cwd=root,text=True).strip()
def project_name(s):return isinstance(s,str) and NAME.fullmatch(s) is not None

def package_roots(root):
 roots=[root];p=root/'lake-manifest.json'
 if p.exists():
  d=json.loads(p.read_text());packages=root/d.get('packagesDir','.lake/packages')
  for x in d['packages']:
   if x['name']=='mathlib':continue
   q=root/x['dir'] if x['type']=='path' else packages/x['name']
   if q.exists():roots.append(q)
 return list(dict.fromkeys(roots))

def pinned_git_packages(root):
 d=json.loads((root/'lake-manifest.json').read_text())
 packages=root/d.get('packagesDir','.lake/packages')
 return {x['name']:{'path':os.path.relpath(packages/x['name'],root),
   'expected_commit':x['rev']} for x in d['packages'] if x['type']=='git'}

def check_git_packages(root,expected):
 identities={}
 for name,x in expected.items():
  pkg=root/x['path'];head=git(pkg,'rev-parse','HEAD')
  tracked=git(pkg,'status','--porcelain','--untracked-files=no')
  assert head==x['expected_commit'],f'{name}: pinned package revision mismatch'
  assert not tracked,f'{name}: tracked package sources are dirty'
  identities[name]={'path':x['path'],'expected_commit':x['expected_commit'],
    'actual_commit':head,'tracked_status':tracked}
 return identities

def modules_and_declarations(root):
 modules={};decls=collections.defaultdict(set)
 for pkg in package_roots(root):
  for prefix in PROJECT_PREFIXES:
   files=list((pkg/prefix).rglob('*.lean')) if (pkg/prefix).is_dir() else []
   if (pkg/(prefix+'.lean')).is_file():files.append(pkg/(prefix+'.lean'))
   for p in files:
    mod=str(p.relative_to(pkg).with_suffix('')).replace('/','.')
    if mod in modules and modules[mod]!=p:continue
    modules[mod]=p;stack=[]
    for raw in p.read_text().splitlines():
     line=raw.strip();n=re.match(r'namespace\s+([\w.]+)',line)
     if n:stack.append(('ns',n.group(1)));continue
     if re.match(r'(?:noncomputable\s+)?section(?:\s|$)',line):stack.append(('section',''));continue
     if re.match(r'end(?:\s+[\w.]+)?\s*$',line):
      if stack:stack.pop()
      continue
     line=re.sub(r'^@\[[^]]*\]\s*','',line)
     m=re.match(r'(?:(private|protected)\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|structure|class|inductive|abbrev|opaque|axiom|instance)\s+([\w.\']+)',line)
     if not m or m.group(1)=='private':continue
     ns='.'.join(v for k,v in stack if k=='ns');name=(ns+'.' if ns else '')+m.group(2)
     if project_name(name):decls[name].add(mod)
 return modules,decls

def imported_modules(modules,seeds):
 seen=set();q=list(seeds);missing=[]
 while q:
  m=q.pop()
  if m in seen:continue
  if m not in modules:
   if m.startswith(PROJECT_PREFIXES):missing.append(m)
   continue
  seen.add(m)
  q+=re.findall(r'^import\s+([\w.]+)',modules[m].read_text(),re.M)
 return seen,sorted(set(missing))

def providers(name,decls,modules):
 if name.startswith('_private.'):
  return sorted(m for m in modules if name.startswith('_private.'+m+'.') and
    name[len('_private.'+m+'.'):].split('.')[0].isdigit())
 n=name
 while n:
  if n in decls:return sorted(decls[n])
  n=n.rpartition('.')[0]
 return []

def harvest(path,decls):
 data=json.loads(path.read_text());found=[];unknown=[]
 def extract(v,pointer,status,field):
  if isinstance(v,str):
   if project_name(v):found.append({'name':v,'pointer':pointer,'field':field,'recorded_status':status})
   elif re.fullmatch(r"[A-Za-z_][\w']*",v):
    candidates=sorted(n for n in decls if n.endswith('.'+v))
    if len(candidates)==1:found.append({'name':candidates[0],'pointer':pointer,'field':field,'recorded_status':status,'unqualified_original':v})
    else:unknown.append({'value':v,'pointer':pointer,'field':field,'candidates':candidates})
   else:unknown.append({'value':v,'pointer':pointer,'field':field,
     'reason':'Target-bearing field is not a recognized project declaration name'})
  elif isinstance(v,list):
   for i,x in enumerate(v):extract(x,pointer+'/'+str(i),status,field)
  elif isinstance(v,dict):
   for k,x in v.items():
    if project_name(k):found.append({'name':k,'pointer':pointer+'/'+k,'field':field,'recorded_status':status})
    if k in NAME_KEYS:extract(x,pointer+'/'+k,status,k)
 def walk(v,pointer='',status=None):
  if isinstance(v,dict):
   status=v.get('status',status)
   for k,x in v.items():
    if k in SKIP or k.startswith('historical_'):continue
    if k in NAME_KEYS:extract(x,pointer+'/'+k,status,k)
    if isinstance(x,(dict,list)):walk(x,pointer+'/'+k,status)
  elif isinstance(v,list):
   for i,x in enumerate(v):walk(x,pointer+'/'+str(i),status)
 if path.name=='statements.json':
  # Open headline candidates are not public root-export requirements.
  for i,s in enumerate(data['statements']):
   if str(s.get('status','')).startswith(('proved','checked','kernel_checked')):walk(s,'/statements/'+str(i),s.get('status'))
 else:walk(data)
 # Repeated type bindings provide provenance but not additional targets.
 return found,unknown

def render(imports,names,presence=False):
 header=''.join('import '+m+'\n' for m in dict.fromkeys(imports))+'import Lean.Util.CollectAxioms\nimport Lean.Elab.Command\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option pp.all true\n'
 target_lines=',\n'.join('    '+json.dumps(n,ensure_ascii=False) for n in names)
 setup='''open Lean Elab Command in
run_cmd do
  let requested : Array String := #[
'''+target_lines+''']
  let env ← getEnv
  let allNames := env.constants.toList.foldl (fun acc (n, _) => acc.insert n.toString n)
    ({} : Std.HashMap String Name)
'''
 if presence:return header+setup+'''  let missing := requested.filter fun n => !(allNames.contains n)
  let mut present : Array Json := #[]
  for s in requested do
    if let some n := allNames[s]? then
      let mod := (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?
      present := present.push <| Json.mkObj [("name", toJson s),
        ("kernel_import_module", toJson (mod.map Name.toString))]
  IO.println <| (Json.mkObj [("requested", toJson requested), ("missing", toJson missing),
    ("present", Json.arr present)]).compress
'''
 body='''  let targets ← requested.mapM fun s => do
    match allNames[s]? with
    | some n => pure n
    | none => throwError "Missing exact mapped declaration: {s}"
  -- Checking the complete union implies that every individual target closure
  -- contains only allowed axioms; the shared visited state avoids replay.
  let (_, axiomState) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  let forbidden := axiomState.axioms.filter fun n =>
    !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n
  unless forbidden.isEmpty do throwError "Unexpected kernel axiom in mapped union: {forbidden}"
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := (ci.type.getUsedConstants ++
      (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])).toList.eraseDups.toArray
    let projectDeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" || s.startsWith "Kane" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining" ||
        s.startsWith "_private.Kane"
    graph := graph.push <| Json.mkObj [("name", toJson target.toString),
      ("direct_project_dependencies", toJson (projectDeps.map Name.toString))]
    queue := projectDeps.toList ++ queue
    if targets.contains target then
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      let mod := (env.getModuleIdxFor? target).bind fun i => env.header.moduleNames[i.toNat]?
      endpoints := endpoints.push <| Json.mkObj [("name", toJson target.toString),
        ("expanded_type", toJson ty), ("direct_dependencies", toJson (deps.map Name.toString)),
        ("kernel_import_module", toJson (mod.map Name.toString))]
  IO.println <| (Json.mkObj [("scope", toJson "Exact fresh mapped types and kernel project graph; no blanket legacy-CLT exclusion"),
    ("axiom_strategy", toJson "One complete shared kernel axiom-union over every requested declaration; allowed union implies each closure is allowed"),
    ("axiom_union", toJson (axiomState.axioms.map Name.toString)),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
'''
 return header+setup+body

def plan(args):
 root=args.root.absolute();out=args.out.absolute();out.mkdir(parents=True,exist_ok=False)
 modules,decls=modules_and_declarations(root);root_closure,missing_modules=imported_modules(modules,['RectangleCLTArxivV1'])
 ledgers=sorted((root/'correspondence').glob('*-passages.json'))+[root/'correspondence/statements.json']
 exclude=dict(DEFAULT_EXCLUSIONS)
 if args.exclusions:exclude.update(json.loads(args.exclusions.read_text()))
 origins=collections.defaultdict(list);unknown=[];ledger_hashes={};excluded={};notes=[]
 for p in ledgers:
  rel=str(p.relative_to(root))
  if rel in exclude:
   old_names,old_unknown=harvest(p,decls)
   excluded[rel]={'sha256':sha(p),'reason':exclude[rel],
     'historical_mapped_names':sorted({x['name'] for x in old_names}),
     'unresolved_historical_values':old_unknown}
   continue
  ledger_hashes[rel]=sha(p);found,unc=harvest(p,decls)
  for x in found:origins[x['name']].append({'ledger':rel,**{k:v for k,v in x.items() if k!='name'}})
  for x in unc:
   if NON_DECLARATION_NOTES.get((p.name,x['pointer']))==x['value']:
    acceptance='correspondence/c2-acceptance.json'
    ledger_hashes[acceptance]=sha(root/acceptance)
    notes.append({'ledger':rel,**x,'classification':'Exact historical prose note, not a Lean declaration name. Its entire ledger hash remains pinned.',
      'supersession_review':'Root explicitly confirmed this classification and exact checked supersession endpoints; the historical ledger remains unchanged.',
      'checked_supersession_endpoints':NOTE_SUPERSESSION_ENDPOINTS,
      'existing_acceptance':{'path':acceptance,'sha256':sha(root/acceptance)}})
    for n in NOTE_SUPERSESSION_ENDPOINTS:
     origins[n].append({'ledger':rel,'pointer':x['pointer'],
       'field':'explicit_reviewed_historical_note_supersession',
       'recorded_status':'Checked exact C2 supersession, not a declaration inferred from prose'})
   else:unknown.append({'ledger':rel,**x})
 names=sorted(origins);provider_map={n:providers(n,decls,modules) for n in names}
 extras=set()
 for n,ms in provider_map.items():
  if not set(ms)&root_closure and len(ms)==1:extras.add(ms[0])
 all_mods,extra_missing=imported_modules(modules,root_closure|extras)
 source_files={os.path.relpath(modules[m],root):sha(modules[m]) for m in sorted(all_mods)}
 for pkg in package_roots(root):
  if not any(p.is_relative_to(pkg) for m,p in modules.items() if m in all_mods):continue
  for config in ['lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain']:
   p=pkg/config
   if p.is_file():source_files[os.path.relpath(p,root)]=sha(p)
 for x in excluded.values():
  x['names_not_requested_elsewhere']=sorted(set(x['historical_mapped_names'])-set(names))
 data={'status':'PREPARED_REGENERATE_AFTER_FINAL_ROOT_INTEGRATION','created_at_utc':now(),'scope':'Every actual mapped name in current pending/accepted detailed passage ledgers plus accepted headline records. This plan neither registers passages nor changes Root/Audit.','root_module':'RectangleCLTArxivV1','source_commit':git(root,'rev-parse','HEAD'),'ledger_sha256':ledger_hashes,'excluded_historical_ledgers':excluded,'target_count':len(names),'target_origins':origins,'unresolved_unqualified_values':unknown,'module_provider_candidates':provider_map,'root_project_import_closure':sorted(root_closure),'candidate_extra_imports':sorted(extras),'unresolved_project_imports':sorted(set(missing_modules+extra_missing)),'source_identity':source_files,'source_module_paths':{m:os.path.relpath(modules[m],root) for m in sorted(all_mods)},'axiom_strategy':'Lean.CollectAxioms.collect once over all requested targets with a shared visited-state; standard-three union implies standard-three per target.','allowed_axioms':['propext','Classical.choice','Quot.sound'],'no_blanket_archived_final_CLT_exclusion':True,'method_variation_note':'Lower scalar Berry--Esseen specialization through a checked foundation bounded CLT must stay explicitly disclosed. Main-target no-legacy-CLT checks are separate, endpoint-specific assertions.','execution_preconditions':['Final proof-source/ledger checkpoint committed and Root/Audit headline imports integrated.','Separate clean checkout at source_commit; matching selected source and ledger hashes.','Dependency cache/toolchain prepared with pinned package identity.','No requested target is silently dropped; unresolved/missing/ambiguous targets fail and remain reviewable.']}
 data['mapping_tool_identity']={'path':os.path.relpath(Path(__file__).resolve(),root),
   'sha256':sha(__file__)}
 data['pinned_git_packages']=pinned_git_packages(root)
 data['non_declaration_notes']=notes
 data['harvest_policy_note']='Archived baseline statement archive_candidate records and historical dependency inventories are not mapped targets. Explicit checked archived_declaration_candidates in passage rows remain targets. Actual target kernel dependencies are never excluded by this metadata policy.'
 put(out/'plan.json',data);put(out/'requested-targets.json',names)
 (out/'TypesAndAudit.lean').write_text(render(['RectangleCLTArxivV1']+sorted(extras),names))
 print(json.dumps({'plan':str(out/'plan.json'),'ledgers':len(ledger_hashes),'targets':len(names),'root_modules':len(root_closure),'candidate_extra_imports':len(extras),'unresolved_unqualified_values':len(unknown),'missing_provider_names':sum(not x for x in provider_map.values())}))

def parse_log(p,key):
 rows=[]
 for line in p.read_text().splitlines():
  if line.startswith('{'):
   try:d=json.loads(line)
   except json.JSONDecodeError:continue
   if key in d:rows.append(d)
 if len(rows)!=1:raise RuntimeError(f'Expected one {key} JSON export in {p}, found {len(rows)}')
 return rows[0]

def run(args):
 planfile=args.plan.absolute();d=json.loads(planfile.read_text());root=args.clean_root.absolute();out=args.out.absolute();out.mkdir(parents=True,exist_ok=False)
 assert not git(root,'status','--porcelain'),'Clean checkout required'
 assert git(root,'rev-parse','HEAD')==d['source_commit'],'Plan commit differs; regenerate after final integration'
 r={'status':'running','scope':'Fresh selected full-clean Root build/source replay, exact mapped types and shared complete kernel axiom union. No headline acceptance is performed.','initial_git_status':'','source_commit':d['source_commit'],'plan_sha256':sha(planfile),'axiom_strategy':d['axiom_strategy'],'allowed_axioms':d['allowed_axioms'],'no_blanket_archived_final_CLT_exclusion':True,'commands':[],'started_at_utc':now()}
 def save():put(out/'run.json',r)
 env=os.environ.copy();env['PATH']='/workspace/lean-toolchain-bin/bin:'+env['PATH']
 def command(label,argv):
  p=out/(label+'.log');x={'label':label,'argv':argv,'started_at_utc':now(),'log':str(p)};r['commands'].append(x);save()
  with p.open('wb') as f:q=subprocess.run(argv,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
  x.update(exit_code=q.returncode,finished_at_utc=now(),log_sha256=sha(p));save()
  if q.returncode:raise RuntimeError(label+' failed; receipt/log preserved')
 def validate(allow_missing_packages=False):
  for p,h in {**d['ledger_sha256'],**d['source_identity']}.items():
   f=root/p
   if allow_missing_packages and not f.exists() and p.startswith('.lake/'):continue
   assert f.is_file() and sha(f)==h,p
 try:
  save()
  assert not d['unresolved_unqualified_values'],'Unresolved ledger names must be reviewed before execution'
  assert sha(__file__)==d['mapping_tool_identity']['sha256'],'Mapping tool changed; regenerate plan'
  validate(True)
  put(out/'initial-pinned-package-identities.json',check_git_packages(root,d['pinned_git_packages']))
  command('toolchain-version',['lake','env','lean','--version'])
  toolchain=(root/'lean-toolchain').read_text().strip().split(':')[-1].removeprefix('v')
  assert ('version '+toolchain+',') in (out/'toolchain-version.log').read_text(),\
    'Actual Lean version differs from pinned lean-toolchain'
  command('build-root',['lake','build',d['root_module']])
  names=sorted(d['target_origins']);presence=out/'Presence.lean';presence.write_text(render([d['root_module']],names,True));command('presence',['lake','env','lean',str(presence)])
  missing=parse_log(out/'presence.log','missing')['missing'];extra=set();unresolved=[]
  for n in missing:
   ps=d['module_provider_candidates'][n]
   if len(ps)==1:extra.add(ps[0])
   else:unresolved.append({'name':n,'providers':ps})
  put(out/'presence.json',{'missing_from_root':missing,'extra_imports':sorted(extra),'unresolved':unresolved})
  assert not unresolved,'Missing/ambiguous mapped providers; review presence.json, do not drop targets'
  if extra:command('build-extras',['lake','build']+sorted(extra))
  resolved=out/'ProviderPresence.lean'
  resolved.write_text(render([d['root_module']]+sorted(extra),names,True))
  command('provider-presence',['lake','env','lean',str(resolved)])
  actual=parse_log(out/'provider-presence.log','missing')
  assert not actual['missing'],'Targets still missing after explicit provider imports'
  assert {x['name'] for x in actual['present']}==set(names),'Provider presence omitted targets'
  actual_providers={x['kernel_import_module'] for x in actual['present']}
  assert None not in actual_providers,'Requested mapped declaration has no imported kernel module'
  assert all(m in d['source_module_paths'] for m in actual_providers),\
    'Actual imported mapped provider lacks a pinned project source; regenerate/review plan'
  put(out/'actual-provider-bindings.json',actual)
  # Replay every ArxivV1 source in Root plus selected-extra import closures,
  # including intermediate ArxivV1 imports of an extra provider. Explicit
  # external provider files are also replayed, without replacing proof source.
  modules,_=modules_and_declarations(root)
  selected_closure,missing_imports=imported_modules(modules,[d['root_module']]+sorted(extra))
  assert not missing_imports,missing_imports
  force=[m for m in selected_closure if m.startswith('RectangleCLTArxivV1')]
  force=sorted(set(force)|extra|actual_providers)
  put(out/'forced-source-inventory.json',{'scope':'All ArxivV1 sources in Root/selected-extra closure and every actual imported mapped provider, including archive/foundation/GenericChaining/Kane providers.','modules':force,'source_sha256':{m:d['source_identity'][d['source_module_paths'][m]] for m in force}})
  for i,m in enumerate(force):command(f'force-{i:04d}-'+m.replace('.','-'),['lake','env','lean',d['source_module_paths'][m]])
  harness=out/'TypesAndAudit.lean';harness.write_text(render([d['root_module']]+sorted(extra),names));command('types-and-axiom-union',['lake','env','lean',str(harness)])
  x=parse_log(out/'types-and-axiom-union.log','endpoints');assert {e['name'] for e in x['endpoints']}==set(names)
  assert {e['kernel_import_module'] for e in x['endpoints']}==actual_providers,\
    'Kernel provider identities drifted between presence and full-type export'
  put(out/'expanded-types-and-dependencies.json',x);lookup={e['name']:e for e in x['endpoints']}
  put(out/'ledger-bindings.json',{'ledger_sha256':d['ledger_sha256'],'export_sha256':sha(out/'expanded-types-and-dependencies.json'),'scope':'Fresh type/dependency binding, not semantic passage promotion','bindings':{n:{'origins':d['target_origins'][n],'expanded_type':lookup[n]['expanded_type'],'kernel_import_module':lookup[n]['kernel_import_module']} for n in names}})
  validate()
  put(out/'final-pinned-package-identities.json',check_git_packages(root,d['pinned_git_packages']))
  assert not git(root,'status','--porcelain'),'Clean source checkout drifted'
  r.update(status='passed',target_count=len(names),project_dependency_nodes=len(x['project_dependency_graph']),axiom_union=x['axiom_union'],export_sha256=sha(out/'expanded-types-and-dependencies.json'),bindings_sha256=sha(out/'ledger-bindings.json'),finished_at_utc=now());save()
 except Exception as e:r.update(status='failed',failure=str(e),finished_at_utc=now());save();raise
 print(json.dumps({'status':'passed','targets':r['target_count'],'graph_nodes':r['project_dependency_nodes']}))

def main():
 parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='command',required=True)
 p=sub.add_parser('plan');p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--out',type=Path,required=True);p.add_argument('--exclusions',type=Path);p.set_defaults(action=plan)
 p=sub.add_parser('run');p.add_argument('--plan',type=Path,required=True);p.add_argument('--clean-root',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.set_defaults(action=run)
 args=parser.parse_args();args.action(args)
if __name__=='__main__':main()

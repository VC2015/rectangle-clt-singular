#!/usr/bin/env python3
"""Narrow H.1 printed-proof addendum: record a candidate, then apply its exact hash.

Neither command runs Lean or replaces the historical443/1949 acceptance.
Record writes only a new evidence directory. Apply changes only the seven
listed metadata files and one new completion record after rechecking inputs.
"""
import argparse, copy, datetime, hashlib, json, os, re, runpy, subprocess
from pathlib import Path

N='RectangleCLTArxivV1.'
COMMIT='63c975b7bd2176ddf559dbed1b2e087e191f7a45'
BASE='443fbc667ed3c3ee47369e028c2c4280a5eed604'
ALLOWED={'propext','Classical.choice','Quot.sound'}
META=['STATUS.md','README.md','correspondence/README.md','correspondence/final-acceptance.json','correspondence/final-coverage.json','correspondence/proof-environments.json','correspondence/statements.json']
COMPLETION='correspondence/supplemental-h-nonsimple-printed-completion.json'
E='evidence/supplemental-h-nonsimple-printed/'
REVIEWS={
'pointwise_green':E+'independent-archive-review.json',
'actual_spherical':'evidence/supplemental-h-nonsimple-face-coordinates/independent-root-review.json',
'generic_spherical':'evidence/supplement-h-spherical-polygon/independent-bounded-review.json',
'finite_chart':'evidence/supplemental-h-nonsimple-finite-chart-mass/independent-bounded-review.json',
'prior_q3_chart':'evidence/supplemental-h-nonsimple-face-chart-mass/independent-root-review.json',
'clean_runtime':E+'clean-independent-archive-review.json',
'ridge_green_support':'evidence/supplemental-h-nonsimple-ridge-green/independent-root-support-review.json',
'common_mass':'evidence/supplement-h-nonsimple-common-mass/independent-g3-review.json',
'base_geometry':'evidence/supplemental-h-nonsimple-face-geometry/independent-review.json',
'selected_actual_faces':'evidence/supplemental-h-nonsimple-face-selected/independent-archive-review.json',
'retained_facets':'evidence/supplemental-h-nonsimple-face-retained/independent-bounded-review.json',
'incidence_geometry':'evidence/supplemental-h-nonsimple-face-incidences/independent-review.json',
'cone_polar':'evidence/supplemental-h-nonsimple-cone-polar-independent/independent-review.json',
'spherical_polar':'evidence/supplement-h-spherical-polygon-polar/independent-review.json',
'square_cone':'evidence/supplemental-h-nonsimple-square-balance/independent-g3-review.json',
'local_analytic':'evidence/supplemental-h-nonsimple-ridge-green/integrated/independent-child-review.json',
'local_canonical':'evidence/supplemental-h-nonsimple-ridge-green/canonical/independent-child-review.json',
'local_actual':'evidence/supplemental-h-nonsimple-ridge-green/actual/independent-child-review.json',
'clean_tooling':'evidence/h1-printed-clean-tools/independent-archive-review.json'}
CORE=['hardGaussianWeightedRidgeIntegral_Green_actualFaces','exists_actual_facet_ridge_Green',
'nonsimpleActualConormalSum_eq_spherical_vector','nonsimpleActualConormalSum_norm_le_spherical_area',
'nonsimpleActualGaussianMass_eq_surface_integral','nonsimpleActualGaussianMass_eq_finite_surface_integral',
'nonsimpleActualGaussianMass_ridge_surface_integral','nonsimpleSquare_printed_ridge_Green',
'nonsimpleSquare_actualVertex_printed_spherical_balance','nonsimpleSquare_actualVertex_printed_spherical_norm_bound']
SCOPE='The actual all-threshold empty-or-topologically-full-dimensional surface bound retains its checked fixed-actual-facet value-continuity/Fatou proof. The actual-facet pointwise nonsimple ridge Green identity and complete arbitrary-edge spherical conormal identity are separately proved and bound in the nonsimple completion addendum. Chart surface and polar angular measures use the documented Euclidean normalization.'
NOTE='The formerly bypassed pointwise ridge Green identity and arbitrary-edge spherical conormal formula are separately checked for complete actual faces. The earlier generic-threshold/Fatou route remains a distinct checked alternative. Chart Lebesgue and polar surface conventions are explicit; no raw unnormalized Mathlib Hausdorff identification is asserted.'
SUMMARY='All 40 named results retain their checked concrete types: 39 unqualified and E.1 explicitly qualified by A ≥ 0; all 34 proof environments retain their reviewed bindings. The formerly bypassed H.1 pointwise nonsimple Green identity and arbitrary-edge spherical identities are separately completed in the post-acceptance addendum. Older alternative proofs and their scope are preserved.'
DOC_SCOPE='The pointwise nonsimple ridge Gauss–Green identity at supplement 1081–1100 and the arbitrary-edge spherical conormal identity at 1101–1132 are separately proved for complete actual faces. The existing all-threshold H.1 bound retains its checked continuity/Fatou proof. The spherical identity uses Gaussian first-moment and polar integration, with the documented Euclidean chart and polar measure convention; no raw unnormalized Hausdorff identification is asserted.'

def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def dump(p,x):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def ref(root,p):
    p=Path(p).resolve();return {'path':os.path.relpath(p,root),'sha256':sha(p)}
def bound(root,p,h):require((root/p).is_file() and sha(root/p)==h,'Changed/missing evidence: '+str(p))
def pointer(d,p):
    for k in p.split('/')[1:]:
        k=k.replace('~1','/').replace('~0','~');d=d[int(k)] if isinstance(d,list) else d[k]
    return d

def old_snapshots(root,m):
    r=m['immutable_old_pre_acceptance_manifest']['manifest'];bound(root,r['path'],r['sha256'])
    manifest=read(root/r['path']);home=(root/r['path']).parent/'pre-acceptance'
    require(len(manifest)==m['immutable_old_pre_acceptance_manifest']['file_count']==89,'Old snapshot count changed')
    require({str(p.relative_to(home))for p in home.rglob('*')if p.is_file()}==set(manifest),'Old snapshot file set changed')
    for p,h in manifest.items():require(sha(home/p)==h,'Old saved preimage changed: '+p)

def baseline(root):
    m=read(root/E/'metadata-input-manifest.json');q=read(root/E/'metadata-supersession-proposal.json')
    require(q['baseline_manifest']==ref(root,root/E/'metadata-input-manifest.json'),'Proposal baseline manifest changed')
    require(set(m['baseline_global_preimage_sha256'])==set(META),'Unexpected metadata mutation set')
    for p,h in m['baseline_global_preimage_sha256'].items():bound(root,p,h)
    require(len(m['immutable_old_frozen_passage_ledgers'])==75,'Old ledger inventory changed')
    for p,h in m['immutable_old_frozen_passage_ledgers'].items():bound(root,p,h)
    for r in m['immutable_old_final_acceptance_inputs'].values():bound(root,r['path'],r['sha256'])
    old_snapshots(root,m)
    cache={}
    for row in q['current_assertion_fields']+q['historical_scope_fields_to_preserve']:
        if row['path']not in cache:cache[row['path']]=read(root/row['path'])
        require(pointer(cache[row['path']],row['json_pointer'])==row['current_value'],'Old pointer changed: '+row['json_pointer'])
    require(not (root/COMPLETION).exists(),'Completion already exists; do not apply twice')
    a=read(root/'correspondence/final-acceptance.json')
    require(a['counts']==dict(unqualified_statements=39,qualified_statements=1,excluded_conjectures=1,proof_environments=34),'Named-result scope changed')
    require(a['coverage_counts']['all_exact_mapped_declarations']==1949 and not a['release_wide_unqualified_certification'] and not a['every_literal_printed_internal_claim_certified'],'Historical scope changed')
    return m,q

def verify_clean(root,path):
    path=Path(path).resolve();r=read(path);home=path.parent
    require(r['status']=='passed' and r['initial_git_status']=='' and r['source_commit']==COMMIT and r['baseline_source_commit']==BASE,'Not the passed clean proof checkpoint')
    require(r['historical_1949_target_mapping_replayed'] is False and r['source_identity']==r['final_source_identity'],'Clean identity/scope changed')
    for p,h in r['source_identity'].items():bound(root,p,h)
    logs={}
    for c in r['commands']:
        require(c.get('exit_code')==0,'Unfinished/failed command: '+c['label'])
        p=Path(c['log']);p=p if p.is_absolute() else home/p
        require(sha(p)==c['log_sha256'],'Changed log: '+str(p));require(c['label']not in logs,'Duplicate command label');logs[c['label']]=(c,p)
    need={'lean-version','pins','frozen-source-ledger','library-and-extension-build','force-root','registered-axiom-audit','mapped-supplement-H','new-full-types-and-axiom-audit','registered-types-and-dependencies'}
    require(need<=set(logs),'Missing clean stage')
    require(sha(home/'NewTypesAndAudit.lean')==r['harness_sha256'],'New Lean harness changed')
    forced=r['forced_modules'];require(len(forced)==len(set(forced))==66,'Wrong forced module set')
    require(logs['library-and-extension-build'][0]['argv']==['lake','build','RectangleCLTArxivV1']+forced,'Wrong integrated library build')
    require(logs['force-root'][0]['argv']==['lake','env','lean','RectangleCLTArxivV1.lean','-o','.lake/build/lib/lean/RectangleCLTArxivV1.olean'],'Wrong Root source replay')
    new=r['new_or_changed_native_sources'];old=r['unchanged_baseline_native_sources']
    require(not set(new)&set(old),'Overlapping native source sets')
    tracked=subprocess.check_output(['git','ls-files','-z','--','RectangleCLTArxivV1'],cwd=root).decode().split('\0')
    live={p:sha(root/p)for p in tracked if p.startswith('RectangleCLTArxivV1/') and p.endswith('.lean')}
    require(live==old|new,'Native file set/bytes changed')
    require({p[:-5].replace('/','.')for p in new}==set(forced),'Force list differs from changed/new sources')
    for module in forced:
        c,_=logs['force-'+module.rsplit('.',1)[-1]];src=module.replace('.','/')+'.lean'
        require(c['argv']==['lake','env','lean',src,'-o','.lake/build/lib/lean/'+module.replace('.','/')+'.olean'],'Wrong source force: '+module)
    catalog=runpy.run_path(str(root/'tools/prepare_full_clean_mapping.py'))
    modules,decls=catalog['modules_and_declarations'](root)
    expected=sorted(n for n,providers in decls.items()if providers&set(forced))
    require(len(expected)==537 and r['new_public_targets']==expected,'Public target set differs from source providers')
    x=read(logs['new-full-types-and-axiom-audit'][1]);end={e['name']:e for e in x['endpoints']}
    require(len(x['endpoints'])==r['new_public_expanded_types']==537 and set(end)==set(expected),'Incomplete/duplicate fulltypes')
    require(set(x['axiom_union'])==ALLOWED and set(r['new_axiom_union'])==ALLOWED,'Unexpected/incomplete kernel axiom union')
    require('shared' in x['axiom_strategy'].lower(),'Unexpected shared transitive audit method')
    graph={e['name']:set(e['direct_project_dependencies'])for e in x['project_dependency_graph']}
    require(len(graph)==len(x['project_dependency_graph'])==r['new_project_dependency_nodes'] and all(ds<=set(graph)for ds in graph.values()) and set(expected)<=set(graph),'Open/incomplete project graph')
    for n,e in end.items():
        require(e['expanded_type'] and decls[n]=={e['kernel_import_module']} and e['kernel_import_module']in forced,'Wrong exact kernel provider: '+n)
        src=e['kernel_import_module'].replace('.','/')+'.lean';require(src in new and new[src]==sha(root/src),'Unreplayed provider: '+n)
    require(all(N+n in end for n in CORE),'Missing completion endpoint')
    deps=read(logs['registered-types-and-dependencies'][1]);dg={e['name']:set(e['direct_project_dependencies'])for e in deps['project_dependency_graph']}
    require(len(deps['endpoints'])==r['registered_expanded_types'] and len(dg)==r['registered_project_dependency_nodes'] and all(ds<=set(dg)for ds in dg.values()),'Registered graph/type receipt mismatch')
    require(logs['registered-axiom-audit'][1].read_text().count('(shared transitive axiom audit)')==r['registered_axiom_audit_targets']>0,'Registered audit missing')
    for k in ['dependency','native']:
        cp=r['cache_preparation'];p=Path(cp[k+'_receipt']);require(sha(p)==cp[k+'_receipt_sha256'],'Cache preparation receipt changed')
    require(r['cache_preparation']['new_native_artifacts_reused']is False,'New proof artifacts were cached')
    require(all(d['expected_commit']==d['actual_commit'] and not d['tracked_status']for d in r['git_dependencies'].values()),'Unpinned/dirty dependency')
    tree=subprocess.check_output(['git','rev-parse',COMMIT+'^{tree}'],cwd=root,text=True).strip();require(tree==r['source_tree'],'Proof commit/tree differs')
    refs={'clean_receipt':ref(root,path),'full_types_graph_and_axioms':ref(root,logs['new-full-types-and-axiom-audit'][1]),'registered_types':ref(root,logs['registered-types-and-dependencies'][1]),'registered_audit':ref(root,logs['registered-axiom-audit'][1]),'new_harness':ref(root,home/'NewTypesAndAudit.lean')}
    return r,x,end,refs

def review_refs(root,overrides,clean_ref):
    paths=REVIEWS|overrides;require(set(REVIEWS)<=set(paths),'Missing review roles')
    result={}
    for role,p in paths.items():
        p=(root/p).resolve();d=read(p);require(d.get('status')in {'PASS','passed'},'Review not passed: '+role)
        result[role]=ref(root,p)
        # Reject changed hash-bearing evidence references, including source maps.
        def walk(v):
            if isinstance(v,dict):
                if isinstance(v.get('path'),str) and re.fullmatch('[0-9a-f]{64}',str(v.get('sha256',''))):
                    if 'lines'in v:
                        candidates={(base/v['path']).resolve()for base in [root,root.parent]if (base/v['path']).is_file()}
                        require(len(candidates)==1,'Missing/ambiguous paper span source in '+role);source=candidates.pop()
                        a,b=v['lines'];lines=source.read_bytes().splitlines(keepends=True)
                        expected=v.get('slice_sha256',v['sha256'])
                        require(1<=a<=b<=len(lines) and hashlib.sha256(b''.join(lines[a-1:b])).hexdigest()==expected,'Changed paper span in '+role)
                        if 'slice_sha256'in v:require(sha(source)==v['sha256'],'Changed complete paper in '+role)
                    else:bound(root,v['path'],v['sha256'])
                for k,h in v.items():
                    if isinstance(h,str) and re.fullmatch('[0-9a-f]{64}',h):
                        if '/'in k and not k.startswith('sha'):bound(root,k,h)
                        elif k.endswith('_sha256') and isinstance(v.get(k[:-7]),str):bound(root,v[k[:-7]],h)
                    if isinstance(h,(dict,list)):walk(h)
            elif isinstance(v,list):
                for h in v:walk(h)
        walk(d)
        if role=='clean_runtime':require(clean_ref['sha256']in json.dumps(d),'Runtime review does not bind this exact clean receipt')
    return result

def render(root,m,q,completion_ref,snapshot,r):
    outputs={p:(root/p).read_bytes()for p in META};docs={p:read(root/p)for p in META if p.endswith('.json')}
    for p in ['correspondence/final-acceptance.json','correspondence/final-coverage.json','correspondence/proof-environments.json']:
        d=docs[p];items=d['literal_unproved_internal_claims'];require(len(items)==1 and items[0]['proof_environment_id']=='P-supplement-27','Unexpected unresolved claims')
        d['historical_bypassed_internal_claims']=[{'pre_completion_record':ref(root,snapshot/p),'historical_live_path':p,'json_pointer':'/literal_unproved_internal_claims/0','record':copy.deepcopy(items[0])}]
        d['literal_unproved_internal_claims']=[]
        d['resolved_printed_internal_claims']=[{'proof_environment_id':'P-supplement-27','status':'checked_separate_pointwise_nonsimple_identity_with_documented_spherical_route','location':items[0]['location'],'completion':completion_ref}]
        d['post_acceptance_addenda']=[completion_ref]
    a=docs['correspondence/final-acceptance.json'];a['statement_promotions'][0]['scope_updated_by']=completion_ref
    a['accepted_output_sha256_scope']='Historical acceptance outputs for proof source commit '+BASE+'; the pre-completion snapshots and new candidate receipt preserve the old and current identities separately.'
    s=docs['correspondence/statements.json'];h=s['statements'][36];require(h['id']=='S-hgap-lem-surfaces','H1 row moved')
    h['printed_proof_status']='checked_statement_with_alternative_route_and_separate_nonsimple_printed_identities';h['formalization_scope']=SCOPE;h['supporting_internal_identities']=completion_ref
    s['final_acceptance']['post_acceptance_addenda']=[completion_ref]
    c=docs['correspondence/final-coverage.json'];p=docs['correspondence/proof-environments.json']
    c['scope']=p['coverage_note']=SUMMARY;c['proof_environments'][26]['scope_notes'][1]=NOTE;p['proof_environments'][26]['final_scope_notes'][1]=NOTE
    c['proof_environments'][26]['printed_internal_completion']=completion_ref;p['proof_environments'][26]['printed_internal_completion']=completion_ref
    changed=0
    for row in q['current_assertion_fields']:
        if row['json_pointer'].endswith('/correspondence_status'):
            target=pointer(c,row['json_pointer'].rsplit('/',1)[0]);require(target['correspondence_status']=='checked_alternative_route_support_with_explicit_H1_internal_bypass','Support classification drift')
            target['correspondence_status']='checked_alternative_route_support_printed_nonsimple_identity_separately_completed';target['separate_printed_completion']=completion_ref;changed+=1
    require(changed==37,'Wrong support classification count')
    c['post_acceptance_scope_supersessions']=[{'json_pointer':v['json_pointer'],'old_value_sha256':hashlib.sha256(v['current_value'].encode()).hexdigest(),'completion':completion_ref}for v in q['historical_scope_fields_to_preserve']]
    for path,d in docs.items():outputs[path]=(json.dumps(d,indent=2,ensure_ascii=False)+'\n').encode()
    status=outputs['STATUS.md'].decode();oldparagraph=next(t for t in status.split('\n\n')if t.startswith('The all-threshold Lemma H.1 bound uses'))
    status=status.replace(oldparagraph,DOC_SCOPE).replace('The final clean proof commit is `'+BASE+'`.','The historical full clean proof commit is `'+BASE+'`.')
    measured='The nonsimple printed extension at proof commit `'+COMMIT+'` passed the clean library build, 66 direct source forces, 537 full public types and their complete standard-three axiom union, with a '+format(r['new_project_dependency_nodes'],',')+'-node closed project graph. The registered audit checked '+str(r['registered_axiom_audit_targets'])+' targets; '+str(r['registered_expanded_types'])+' registered full types have a '+format(r['registered_project_dependency_nodes'],',')+'-node closed graph.'
    status+='\n'+measured+' The separately completed identities are bound in [the completion addendum]('+COMPLETION+'); these measured extension counts do not replace the historical 1,949-target replay.\n';outputs['STATUS.md']=status.encode()
    text=outputs['correspondence/README.md'].decode();oldparagraph=next(t for t in text.split('\n\n')if t.startswith('The all-threshold H.1 statement follows'))
    text=text.replace(oldparagraph,DOC_SCOPE+' E.1 still requires a nonnegative envelope budget.');text=text.replace('The 75 frozen','The historical 75 frozen');text+='\n'+measured+' The [nonsimple printed completion addendum](supplemental-h-nonsimple-printed-completion.json) binds this later evidence; the 1,949-name replay remains historical at 443.\n';outputs['correspondence/README.md']=text.encode()
    require(a['accepted_output_sha256']==read(root/'correspondence/final-acceptance.json')['accepted_output_sha256'],'Old output hashes changed')
    require(c['counts']==read(root/'correspondence/final-coverage.json')['counts'],'Historical count enumeration changed')
    require(s['statements'][25]==read(root/'correspondence/statements.json')['statements'][25] and s['statements'][14]==read(root/'correspondence/statements.json')['statements'][14],'E1 or Conjecture changed')
    return outputs

def record(args):
    root=args.root.resolve();out=args.out.resolve();require(out.is_relative_to(root/'evidence') and not out.exists(),'Output must be a NEW evidence directory')
    m,q=baseline(root);r,x,end,fresh=verify_clean(root,args.clean_run)
    reviews=review_refs(root,dict(v.split('=',1)for v in args.review),fresh['clean_receipt'])
    out.mkdir(parents=True);pre={}
    for p in META:
        source=root/p;require(not source.is_symlink(),'Metadata symlink forbidden');dest=out/'pre-completion'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(source.read_bytes());pre[p]=sha(dest)
    dump(out/'pre-completion-manifest.json',{'source_commit':COMMIT,'files':pre})
    obligations=[]
    paper=root.parent/'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex';lines=paper.read_bytes().splitlines(keepends=True)
    for name,a,b,h in [('H1.NONSIMPLE.GREEN',1081,1100,'a30d66ecc1b9b963ba8b5e288cef3c6b42d3ba28171216a0903e82d04d420a96'),('H1.NONSIMPLE.SPHERICAL',1101,1132,'f86f2c31333148fce3171c07fdfecc07814077468709bdb6a0e8e55f469e15b7')]:
        require(hashlib.sha256(b''.join(lines[a-1:b])).hexdigest()==h,'Frozen paper span changed')
        obligations.append({'id':name,'location':{'source':'supplement','path':'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex','lines':[a,b],'sha256':h}})
    completion={'schema_version':1,'status':'checked_separate_printed_identities_with_documented_route','recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proof_source_commit':COMMIT,'baseline_proof_source_commit':BASE,'historical_1949_replay_replaced':False,'named_counts_unchanged':dict(unqualified=39,qualified_E1=1,excluded_conjectures=1,proof_environments=34),'source_obligations_resolved':obligations,'fresh_evidence':fresh,'new_clean_counts':{'forced_sources':66,'public_types':537,'project_dependency_nodes':r['new_project_dependency_nodes'],'registered_audit_targets':r['registered_axiom_audit_targets'],'registered_expanded_types':r['registered_expanded_types'],'registered_project_dependency_nodes':r['registered_project_dependency_nodes']},'axiom_union':x['axiom_union'],'checked_endpoints':[end[N+n]for n in CORE],'independent_reviews':reviews,'historical_acceptance':ref(root,out/'pre-completion/correspondence/final-acceptance.json'),'pre_completion_snapshot':ref(root,out/'pre-completion-manifest.json'),'count_policy':'Two source obligations are resolved. Supporting declarations, examples and chart bridges are not additional paper statements or printed atoms. Old345/192/547 and1949/10585/578 remain their historical enumeration; no revised canonical union count is claimed.','scope_notes':[SCOPE,NOTE,'The Gaussian first-moment/polar proof establishes the spherical vector identity. The literal manifold tangent-field/Laplacian/divergence intermediate calculation at1112–1123 is not separately claimed.','The chart surface convention is Euclidean orthonormal chart volume; no raw unnormalized Hausdorff normalization identity is asserted.'],'metadata_output_identity_is_in_external_candidate_receipt':str(out.relative_to(root)/'receipt.json')}
    require(sha(paper)=='5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb' and sha(paper.with_suffix('.pdf'))=='34fd0ea571b8005646576b933b90a0555d64fe8c385dc98b462ac965c89d7f94','Frozen paper/PDF changed')
    completion['paper_snapshot']='1803366cc994d9facae8e128ee180f68e319486f';completion['frozen_supplement_sources']=[ref(root,paper),ref(root,paper.with_suffix('.pdf'))]
    candidate=out/'outputs'/COMPLETION;dump(candidate,completion);cr={'path':COMPLETION,'sha256':sha(candidate)}
    outputs=render(root,m,q,cr,out/'pre-completion',r);outputs[COMPLETION]=candidate.read_bytes()
    for p,data in outputs.items():dest=out/'outputs'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
    receipt={'status':'recorded_candidate_not_applied','tool':ref(root,Path(__file__)),'baseline_manifest':ref(root,root/E/'metadata-input-manifest.json'),'pointer_proposal':ref(root,root/E/'metadata-supersession-proposal.json'),'pre_completion_manifest':ref(root,out/'pre-completion-manifest.json'),'fresh_evidence':fresh,'review_refs':reviews,'clean_run':str(Path(args.clean_run).resolve()),'reviews':dict(v.split('=',1)for v in args.review),'preimages':pre,'outputs':{p:sha(out/'outputs'/p)for p in outputs}}
    dump(out/'receipt.json',receipt);print(json.dumps({'status':receipt['status'],'receipt':ref(root,out/'receipt.json'),'outputs':len(outputs)}))

def apply(args):
    root=args.root.resolve();candidate=args.candidate.resolve();rp=candidate/'receipt.json';require(sha(rp)==args.approved_receipt_sha256,'Exact approved candidate receipt required');c=read(rp)
    require(c['status']=='recorded_candidate_not_applied' and c['tool']==ref(root,Path(__file__)),'Candidate/tool drift')
    for key in ['baseline_manifest','pointer_proposal','pre_completion_manifest']:bound(root,c[key]['path'],c[key]['sha256'])
    m,_=baseline(root);r,_,_,fresh=verify_clean(root,c['clean_run']);reviews=review_refs(root,c['reviews'],fresh['clean_receipt'])
    require(fresh==c['fresh_evidence'] and reviews==c['review_refs'],'Approved evidence changed')
    require(set(c['preimages'])==set(META) and c['preimages']==m['baseline_global_preimage_sha256'],'Preimage set changed')
    require(set(c['outputs'])==set(META)|{COMPLETION},'Unapproved output path')
    for p,h in c['preimages'].items():require(sha(candidate/'pre-completion'/p)==h and sha(root/p)==h,'Snapshot/current preimage changed')
    require(read(candidate/'pre-completion-manifest.json')['files']==c['preimages'],'Snapshot manifest mismatch')
    for p,h in c['outputs'].items():require(sha(candidate/'outputs'/p)==h,'Candidate bytes changed: '+p)
    changed=[]
    try:
        for p in c['outputs']:
            dest=root/p;require(not dest.is_symlink(),'Output symlink forbidden');temp=dest.with_name(dest.name+'.h1-completion.tmp');require(not temp.exists(),'Existing temporary file');temp.write_bytes((candidate/'outputs'/p).read_bytes());os.replace(temp,dest);changed.append(p)
        for p,h in c['outputs'].items():bound(root,p,h)
        for p,h in m['immutable_old_frozen_passage_ledgers'].items():bound(root,p,h)
        for v in m['immutable_old_final_acceptance_inputs'].values():bound(root,v['path'],v['sha256'])
        old_snapshots(root,m)
        for p,h in r['source_identity'].items():
            if p not in META:bound(root,p,h)
    except Exception:
        for p in reversed(changed):
            if p in c['preimages']:(root/p).write_bytes((candidate/'pre-completion'/p).read_bytes())
            elif p==COMPLETION:(root/p).unlink(missing_ok=True)
        raise
    dump(candidate/'applied.json',{'status':'applied','approved_receipt_sha256':args.approved_receipt_sha256,'proof_source_commit':COMMIT,'output_sha256':c['outputs'],'historical_acceptance_receipts_unchanged':True})
    print(json.dumps({'status':'applied','completion':COMPLETION,'metadata_files':7}))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);s=p.add_subparsers(dest='phase',required=True)
    q=s.add_parser('record');q.add_argument('--clean-run',type=Path,required=True);q.add_argument('--out',type=Path,required=True);q.add_argument('--review',action='append',default=[],metavar='ROLE=PATH');q.set_defaults(fn=record)
    q=s.add_parser('apply');q.add_argument('--candidate',type=Path,required=True);q.add_argument('--approved-receipt-sha256',required=True);q.set_defaults(fn=apply)
    a=p.parse_args();a.fn(a)
if __name__=='__main__':main()

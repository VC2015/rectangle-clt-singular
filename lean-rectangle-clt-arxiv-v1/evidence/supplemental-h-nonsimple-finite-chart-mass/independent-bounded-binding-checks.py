"""Independent read-only frozen-byte/type/axiom checks; executes no Lean."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parents[2]
E=P/'evidence/supplemental-h-nonsimple-finite-chart-mass'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
checks=[]
def ck(n,b,**kw):
    assert b,n
    checks.append(dict(check=n,status='PASS',**kw))
packets=[dict(id='Geometry25',base=P/'evidence/supplemental-h-nonsimple-finite-frame-chart-geometry',src='RectangleCLTArxivV1/SupplementalHNonsimpleFiniteFrameChartGeometry.lean',source_sha='56b4ff197a5c30d345574bb4bdf5de9f08f6cf144fdb9407fd7d0859b60a760a',freeze_sha='5ad2a21188376cf6e1dfa77065819e75f4d165dd6f88e9fa6d17421657f87a85',receipt_sha='9bde632853b03490a7e5a54bc7e8589da52f8ca5962a7175b4af64ffd63abc10',ledger='correspondence/supplemental-h-nonsimple-finite-frame-chart-geometry-passages.json',ledger_sha='48779fdecfa1e783fd26328d38a4f15bc5fa3088e6f3203aa46820f600f4337a',types='04-full-types-dependencies.log',audit='03-strict-audit.log',count=25,nodes=43),dict(id='Mass18',base=E,src='RectangleCLTArxivV1/SupplementalHNonsimpleFiniteFrameChartMass.lean',source_sha='2fe14ad9e9adc53fe7060afa225a11f07e8d64f3e59f0cebde8b3b1f554633cf',freeze_sha='559ebc6f395becc697ae4fdf217462bb17f36e5056c30c36f2c3d817b576350a',receipt_sha='7894077371c91c9c5b4f776342032ad8312705c4d983d9ae3cdbee6fc1e84bf0',ledger='correspondence/supplemental-h-nonsimple-finite-chart-mass-passages.json',ledger_sha='5426de298185d724b86f17a3e29a41367deb303ad4466ecdffdcf8e0c2b7f2e2',types='15-types-dependencies.log',audit='14-audit.log',count=18,nodes=131)]
alltargets=[];uniongraph={};allaxioms=set();exports={}
for p in packets:
    b=p['base']; c=b/'checkpoint-1';f=load(b/'source-freeze.json');r=load(c/'run.json');l=load(P/p['ledger']);x=load(c/p['types']);a=load(c/p['audit'])
    ck(p['id']+'.pins',sha(P/p['src'])==p['source_sha'] and sha(b/'source-freeze.json')==p['freeze_sha'] and sha(c/'run.json')==p['receipt_sha'] and sha(P/p['ledger'])==p['ledger_sha'])
    ck(p['id']+'.freeze_sources_and_upstreams',all(sha(P/s)==h for s,h in (f['sources']|f['upstream_sources']).items()))
    ck(p['id']+'.receipt_bound_source_bytes',r['source_identity']==r['final_source_identity'] and all(sha(P/s)==h for s,h in r['source_identity'].items()))
    if 'fixture_identity' in r:ck(p['id']+'.fixture_bytes',all(sha(c/s)==h for s,h in r['fixture_identity'].items()))
    ck(p['id']+'.four_actual_passed_commands_and_logs',r['status']=='passed' and len(r['commands'])==4 and all(y['exit_code']==0 and sha(P/y['log'])==y['log_sha256'] for y in r['commands']))
    names=['RectangleCLTArxivV1.'+s for s in re.findall(r'^(?:theorem|def|lemma|structure)\s+([A-Za-z0-9_]+)',(P/p['src']).read_text(),re.M)]
    ck(p['id']+'.complete_public_target_types_and_axioms',len(names)==p['count'] and names==r['targets']==[y['name']for y in x['endpoints']]==[y['name']for y in a['targets']] and len(set(names))==p['count'])
    axs=set(z for y in a['targets'] for z in y['transitive_axioms']);allaxioms|=axs
    ck(p['id']+'.standard_three_transitive_axioms',a['all_axioms_allowed'] and axs=={'propext','Classical.choice','Quot.sound'})
    g={y['name']:set(y['direct_project_dependencies'])for y in x['project_dependency_graph']}
    ck(p['id']+'.closed_project_graph',len(g)==p['nodes'] and all(v<=set(g)for v in g.values()) and set(names)<=set(g),nodes=len(g))
    ck(p['id']+'.actual_source_replay',sum(y['argv'][:3]==['lake','env','lean'] and p['src']in y['argv'] and '-o'in y['argv'] for y in r['commands'])==1)
    if p['id']=='Geometry25':ck(p['id']+'.ledger_exact_full_types',len(l['declarations'])==p['count'] and all(l['declarations'].get(y['name'])==y for y in x['endpoints']))
    else:ck(p['id']+'.ledger_exact_declaration_binding',l['passages'][0]['lean_declarations']==names and l['passages'][0]['lean_source_sha256']==p['source_sha'])
    paper=P.parent/'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex';lines=paper.read_bytes().splitlines(keepends=True)
    ck(p['id']+'.frozen_passage_span_bytes',all(hashlib.sha256(b''.join(lines[y['location']['lines'][0]-1:y['location']['lines'][1]])).hexdigest()==y['location']['sha256']for y in l['passages']))
    ck(p['id']+'.overlapping_kernel_graph_consistency',all(k not in uniongraph or uniongraph[k]==v for k,v in g.items()))
    uniongraph.update(g);alltargets+=names;exports[p['id']]={y['name']:y for y in x['endpoints']}
ck('combined43_unique_declarations',len(alltargets)==43 and len(set(alltargets))==43)
ck('combined_graph_closed',all(v<=set(uniongraph)for v in uniongraph.values()),nodes=len(uniongraph))
def closure(n):
    seen=set();todo=[n]
    while todo:
        k=todo.pop()
        if k in seen:continue
        seen.add(k);todo.extend(uniongraph.get(k,set()))
    return seen
head='RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_finite_surface_integral';cl=closure(head)
need=['nonsimpleFiniteFrameSection_chart_gaussian_map','nonsimpleFiniteFrameChart_rotated_section','nonsimpleChartPrefix_gaussian_map','nonsimpleChartAppendEquiv_gaussian_preserving','nonsimpleChartDensity_rotation','nonsimpleChartDensity_append','nonsimpleActualFiniteFaceChart_mem_closedFace_iff','gaussianFrameHardMass_eq_finiteTangentChart_integral']
ck('actual_Gaussian_product_rotation_density_original_event_route',all('RectangleCLTArxivV1.'+n in cl for n in need) and 'RectangleCLT.Companion.SignedSurface.gaussianRotation_standardGaussian_preserving' in cl,endpoint=head,closure_nodes=len(cl))
alias='RectangleCLTArxivV1.nonsimpleActualGaussianMass_ridge_surface_integral'
ck('q2_alias_uses_actual_generic_mass_identity',head in closure(alias) and head in exports['Mass18'][alias]['direct_dependencies'])
geom='RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_isometry'
ck('actual_affine_isometry_is_constructed',{'RectangleCLTArxivV1.nonsimpleFiniteFrameChartAffineIsometry','RectangleCLTArxivV1.nonsimpleFiniteFrameChartTangentIsometry','RectangleCLTArxivV1.nonsimpleFiniteFrameTangentAppend'}<=closure(geom))
ck('proper_Euclidean_surface_integrability_exported','RectangleCLTArxivV1.nonsimpleActualFiniteFaceEuclideanChart_surface_integrable'in exports['Mass18'])
print(json.dumps({'status':'PASS','scope':'Read-only existing frozen checkpoint reconciliation, not a new Lean run or integrated clean certification','public_declarations':43,'per_packet_graph_nodes':[43,131],'combined_existing_graph_nodes':len(uniongraph),'axiom_union':sorted(allaxioms),'checks':checks},indent=2))

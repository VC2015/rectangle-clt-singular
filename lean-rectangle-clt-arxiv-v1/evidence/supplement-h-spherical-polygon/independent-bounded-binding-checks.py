"""Read-only independent identity/type/route checks for the frozen generic packet."""
import datetime, hashlib, json, pathlib, re
P = pathlib.Path(__file__).resolve().parents[2]
E = P / 'evidence/supplement-h-spherical-polygon'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
f = load(E / 'source-freeze.json')
l = load(P / 'correspondence/supplemental-h-spherical-polygon-passages.json')
r = load(E / 'checkpoint-2/run.json')
x = load(E / 'checkpoint-2/15-types-dependencies.log')
a = load(E / 'checkpoint-2/14-audit.log')
checks = []
def check(name, condition, **evidence):
    assert condition, name
    checks.append(dict(check=name, status='PASS', **evidence))
check('pinned frozen source/ledger/receipt/export bytes', sha(E/'source-freeze.json') == '27a102abac2316f933b1cf56a393c20af6a2886ef8eb50e0c695c54345dda2ca' and sha(P/f['ledger']['path']) == f['ledger']['sha256'] and sha(P/f['receipt']['path']) == f['receipt']['sha256'] and sha(P/l['full_type_dependency_export']['path']) == l['full_type_dependency_export']['sha256'])
check('all three live source bytes match freeze and ledger', all(sha(P/p) == v == l['source_identity'][p] for p,v in f['sources'].items()), source_files=3)
check('all bound checkpoint source/harness/config bytes stable', r['source_identity'] == r['final_source_identity'] and all(sha(P/p) == v for p,v in r['source_identity'].items()), bound_files=len(r['source_identity']))
check('six passed actual Lean command receipts and logs', r['status'] == 'passed' and len(r['commands']) == 6 and all(c['exit_code'] == 0 and sha(P/c['log']) == c['log_sha256'] for c in r['commands']))
expected = []
per_file = {}
for p in f['sources']:
    ns = ['RectangleCLTArxivV1.'+n for n in re.findall(r'^(?:theorem|def|lemma|structure)\s+([A-Za-z0-9_]+)', (P/p).read_text(), re.M)]
    per_file[p] = len(ns)
    expected += ns
names = [e['name'] for e in x['endpoints']]
check('all public declarations exported and audited exactly', len(expected) == 29 and expected == r['targets'] == names == [e['name'] for e in a['targets']] and len(set(expected)) == 29, per_file=per_file)
check('ledger full types and direct dependency sets equal kernel export', len(l['declarations']) == 29 and all(l['declarations'].get(e['name']) == e for e in x['endpoints']))
check('all seven support rows bind only exported declarations', len(l['passages']) == 7 and set(n for p in l['passages'] for n in p['mapped_declarations']) == set(expected))
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
union = set(ax for e in a['targets'] for ax in e['transitive_axioms'])
check('transitive axiom union is exactly standard three', a['all_axioms_allowed'] and union == allowed and all(set(e['transitive_axioms']) <= allowed for e in a['targets']), axiom_union=sorted(union))
graph = {e['name']:set(e['direct_project_dependencies']) for e in x['project_dependency_graph']}
check('232-node project graph is closed and includes all targets', len(graph) == 232 and set(names) <= set(graph) and all(ds <= set(graph) for ds in graph.values()), project_dependency_nodes=len(graph))
def closure(n):
    seen, todo = set(), [n]
    while todo:
        q = todo.pop()
        if q in seen: continue
        seen.add(q)
        todo.extend(graph.get(q,set()))
    return seen
cl = closure('RectangleCLTArxivV1.sphericalPolygon_generated_balance')
required = ['sphericalPolygonGeneratedCone_zero_face_eq_wedge', 'sphericalPolygonFacetChart_angular_area', 'sphericalPolygonOutwardNormals_nonparallel', 'supplementalH_spherical_balance_inward', 'positivePlanarWedge_angular_area', 'supplementalH_integral_radial_three', 'supplementalH_integral_radial_two', 'gaussian_hard_polyhedron_firstMoment_kernel']
check('actual support/chart/strict-facet/first-moment/polar routes present', all('RectangleCLTArxivV1.'+n in cl for n in required), balance_closure_nodes=len(cl), required_names=['RectangleCLTArxivV1.'+n for n in required])
end = {e['name']:e for e in x['endpoints']}
ty = end['RectangleCLTArxivV1.sphericalPolygon_generated_balance']['expanded_type']
check('helper full type retains cone completeness and actual integral', all(s in ty for s in ['Iff','sphericalPolygonGeneratedCone','arccos','Measure.toSphere','MeasureTheory.integral']))
paper = P.parent / 'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex'
pdf = paper.with_suffix('.pdf')
lines = paper.read_bytes().splitlines(keepends=True)
check('all seven literal supplement span hashes match frozen bytes', all(hashlib.sha256(b''.join(lines[p['location']['lines'][0]-1:p['location']['lines'][1]])).hexdigest() == p['location']['sha256'] for p in l['passages']), line_span=[1101,1132], span_sha256=l['passages'][0]['location']['sha256'])
check('complete frozen supplement TeX and PDF identity', sha(paper) == '5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb' and sha(pdf) == '34fd0ea571b8005646576b933b90a0555d64fe8c385dc98b462ac965c89d7f94', tex_sha256=sha(paper), pdf_sha256=sha(pdf))
old = load(E/'checkpoint-1/run.json')
check('failed metadata fixture preserved and its Lean commands passed', sha(E/'checkpoint-1/run.json') == f['preserved_historical_checkpoint']['sha256'] and old['status'] == 'failed' and len(old['commands']) == 6 and all(c['exit_code'] == 0 for c in old['commands']))
print(json.dumps(dict(status='PASS', checks=checks), indent=2))

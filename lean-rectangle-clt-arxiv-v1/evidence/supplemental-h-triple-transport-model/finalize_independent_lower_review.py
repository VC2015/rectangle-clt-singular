import datetime,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];O=Path(__file__).resolve().parent;C=O/'independent-lower-checkpoint-1'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def put(p,d):Path(p).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
run=read(C/'run.json');assert run['status']=='passed' and run['full_type_count']==30 and run['dependency_nodes']==383
Lp=R/'correspondence/supplemental-h-triple-transport-model-passages.json';L=read(Lp)
assert sha(Lp)==run['ledger_sha256']=='75fea41cede1f0c7a50e6af20d61d80867104293b460ef59c59b522d81249666'
for p,h in run['source_identity'].items():assert sha(R/p)==h,p
for q in [run,read(O/'checkpoint-1/run.json')]:
 assert q['status']=='passed'
 for x in q['commands']:
  assert x['exit_code']==0,x['label'];assert sha(R/x['log'])==x['log_sha256'],x['log']
D=read(C/'expanded-types.json');E={x['name']:x for x in D['endpoints']};G={x['name']:x['direct_project_dependencies'] for x in D['project_dependency_graph']};N='RectangleCLTArxivV1.'
def closure(n):
 s=set();q=[n]
 while q:
  x=q.pop()
  if x in s:continue
  s.add(x);q+=G.get(x,[])
 return s
specs=[('tripleIncidence_spherical_coefficient_le_threeFace_event',['tripleIncidenceTransportIsometry','tripleIncidenceFrame_orthonormal','tripleIncidenceTransportBasis','tripleIncidenceTransportRay_linearIndependent','tripleIncidenceTransport_cone_eq','tripleIncidenceTransport_cone_measurableSet','tripleIncidenceTransport_cone_smul_iff','tripleCone_spherical_coefficient_le_threeFace_event','fourthThreeFaceRadius_fourth_integrable','adaptive_cone_gaussian_integral_lower_fourth']),('tripleIncidenceTransportEvent_threeFace_integral_sum_le',['independentNormalTripleTransportTuple_injective','tripleIncidenceTransportEvent_integral_sum_le','tripleOrderedEvent_integral_sum_le','tripleOrderedEvent_indicator_sum_le','tripleIncidenceTransport_active_span','tripleIncidenceTransport_active_levels','tripleIncidenceNormalPoint_supporting_levels','tripleIncidenceTransport_cone_eq','fourthThreeFaceRadius_fourth_integrable']),('tripleIncidenceTransport_cone_eq',['tripleIncidenceTransportIsometry_basis','tripleIncidenceTransportRay_linearIndependent','tripleIncidenceFrame_span'])]
routes=[]
for n,req in specs:
 s=closure(N+n);req=[N+x for x in req];assert set(req)<=s,(n,set(req)-s)
 routes.append({'endpoint':N+n,'closure_nodes':len(s),'required_actual_routes':req,'all_present':True})
dep={'status':'passed','scope':'Actual kernel type/value dependencies, not import reachability. Native signed CommonMass/Green grouping and full H1 not claimed.','full_type_count':30,'project_dependency_nodes':383,'checks':routes,'expanded_types_sha256':sha(C/'expanded-types.json')};put(C/'dependency-check.json',dep)
tex=R/'../research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex';pdf=tex.with_suffix('.pdf');assert sha(tex)==L['frozen_supplement_tex_sha256'];assert sha(pdf)==L['frozen_supplement_pdf_sha256'];T=tex.read_bytes().splitlines(keepends=True)
for p in L['passages']:
 a,b=p['frozen_location']['lines'];assert hashlib.sha256(b''.join(T[a-1:b])).hexdigest()==p['frozen_location']['sha256'];assert set(p['endpoints'])<=E.keys()
def ck(i,t):return {'id':i,'status':'PASS','finding':t}
checks=[
ck('native_orthonormal_frame','The actual pair bisector/difference and nonzero third residual construct frame0. LI3 proves pair nondegeneracy and third residual nonzero; the frame orthonormality and span are proved from the original selected normals.'),
ck('actual_synthesis_isometry','The linear isometry is the explicit finite sum of native frame columns. The isometry law follows from orthonormality; no chosen isometry or normal-coordinate law is assumed.'),
ck('true_pulled_rays','The analysis-coordinate rays synthesize exactly to the original selected normals because those normals belong to the actual frame span. Their LI follows by applying the actual injective synthesis map to a zero linear combination.'),
ck('nonorthogonal_basis','Cardinality three equals Euclidean3 finrank, so the three pulled LI rays form a genuine basis. Isometry and original unit norms give unit rays. Orthogonality of these original-normal rays is neither needed nor asserted.'),
ck('actual_normal_point','The point is the actual native three conditioning levels in Euclidean3, and its synthesis is definitionally the actual original normal point. Frame equality/span and all original supporting levels are proved, not supplied.'),
ck('positive_cone_identification','LI3 makes the selected label map injective. Explicit nonnegative coefficient extension along that injection and restriction back to the three labels proves equality of the generated trihedral cone with the complete selected-active outward cone.'),
ck('cone_regularities','Actual dual halfspaces prove cone measurability. Positive-dilation invariance is transported from the genuine nonnegative-coefficient outward cone; no cone regularity supplier remains.'),
ck('actual_event_geometry','The actual event uses all inactive strict inequalities and exactly the three selected active labels. Actual span and supporting levels yield exact stratum, adaptive nearest-base tube, and outer-layer inclusion through previously independently reviewed genuine projection/cone geometry.'),
ck('actual_coefficient_endpoint','The final coefficient is the actual spherical vector integral paired with the actual coordinate point, times the actual normalized three-dimensional density and retained strict Gaussian probability. It uses actual conical Gaussian Fubini transport, with constant6144 exp(3/2), not an assumed mass estimate.'),
ck('actual_radius_and_moment_discharge','The coefficient specialization supplies the true three-face radius, its positivity, continuity, Lipschitz bound, normal-point control, and actual Gaussian fourth-moment integrability. The final family specialization also supplies the actual R4 integrability internally.'),
ck('genuine_LI_index_family','The finite subtype consists of exactly original-normal LI3 tuples and embeds injectively into ordered distinct-label tuples. No frames are requested for dependent triples; the family can be empty in low rank.'),
ck('derived_factor_six','The actual finite-sum endpoint instantiates the checked nearest-base/permutation incidence proof with the constructed isometries, points, spans, levels and cones. Six is derived from Fin3 permutations, not supplied as a multiplicity bound.'),
ck('quantifier_and_residual_scope','Only finite normals, genuine LI3 and unit-normal data remain in the final actual-radius coefficient/family theorems. Generic intermediate radius lemmas retain ordinary explicit radius assumptions. Native CommonMass, conormal grouping, dependent-atom zero and signed1/6 cancellation are separate, as are raw J_e and every-threshold H1.'),
ck('complete_active_triple_scope','The factor6 endpoint sums the explicitly defined complete-active-three event family. No coverage of nonsimple four-or-more-active strata is inferred from this packet, and no full H1 headline is accepted.'),
ck('source_and_rendered_PDF','Frozen TeX1092–1184 and rendered PDF S13–S14 give the normal-space point, normal cone, disjoint short outward tubes and R4 domination. The concrete frame0 and nonorthogonal ray basis are faithful explicit constructions. Prior S12 radius context supplies the actual radius definition; angular measure remains canonical Euclidean-volume-induced sphere measure, without an unproved raw diameter-Hausdorff normalization claim.')]
read_sources=list(L['source_identity'])+['RectangleCLTArxivV1/SupplementalHTripleIncidenceGeometry.lean','RectangleCLTArxivV1/SupplementalHFrameIsometry.lean','RectangleCLTArxivV1/SupplementalHIndependentTriples.lean']
review={'result':'PASS_CONCRETE_NATIVE_LI3_MODEL_AND_ACTUAL_TRANSPORT_ONLY','reviewer':'/root/lower_resume','review_kind':'Independent source/PDF/full-type/kernel-dependency review','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'independence':'Reviewer did not author any four-model or eight abstract triple transport source. Prior G cap bridge/lower-family authorship is outside this packet; the independently reviewed abstract triple72 support is reused with its exact scope.','frozen_ledger':str(Lp.relative_to(R)),'frozen_ledger_sha256':sha(Lp),'historical_ledger_status_note':'Frozen pending-independent-review prose remains byte-identical; this separately stored review closes only the claimed model/support scope.','core_source_sha256':L['source_identity'],'checked_support_source_sha256':run['source_identity'],'independently_read_sources':read_sources,'frozen_supplement_tex_sha256':sha(tex),'frozen_supplement_pdf_sha256':sha(pdf),'rendered_pdf_pages':['S12','S13','S14'],'rendered_pdf_method':'Read pdftotext-layout text of the actual frozen rendered PDF alongside exact TeX and Lean source; same frozen pages previously read for abstract triple review. No typography claim.','author_receipt':{'path':str((O/'checkpoint-1/run.json').relative_to(R)),'sha256':sha(O/'checkpoint-1/run.json')},'independent_receipt':{'path':str((C/'run.json').relative_to(R)),'sha256':sha(C/'run.json')},'independent_full_type_count':30,'independent_project_dependency_nodes':383,'expanded_types':str((C/'expanded-types.json').relative_to(R)),'expanded_types_sha256':sha(C/'expanded-types.json'),'dependency_check':{'path':str((C/'dependency-check.json').relative_to(R)),'sha256':sha(C/'dependency-check.json')},'checked_primary_full_types':[E[N+n] for n in ['tripleIncidence_spherical_coefficient_le_threeFace_event','tripleIncidenceTransportEvent_threeFace_integral_sum_le']],'checks':checks,'passage_results':[{'id':p['id'],'status':'PASS_CLAIMED_CONCRETE_MODEL_INFERENCE_ONLY','frozen_location':p['frozen_location'],'checked_endpoints':p['endpoints']} for p in L['passages']],'unmatched_mathematical_premises_within_claimed_scope':[],'native_CommonMass_and_conormal_grouping_status':'SEPARATE_OUTSIDE_THIS_PACKET','raw_Je_and_full_every_threshold_H1_status':'OPEN','release_wide_certification':False,'source_or_frozen_ledger_edits':False}
put(O/'independent-lower-review.json',review)
paths=[Lp,C/'run.json',C/'expanded-types.json',C/'dependency-check.json',O/'independent-lower-review.json']
put(O/'independent-lower-review-freeze.json',{'status':'passed','scope':review['result'],'created_at_utc':review['reviewed_at_utc'],'source_sha256':run['source_identity'],'artifacts_sha256':{str(p.relative_to(R)):sha(p) for p in paths},'source_or_frozen_ledger_edits':False})
print(json.dumps({'result':review['result'],'checks':len(checks),'types':30,'nodes':383,'route_closure_nodes':[x['closure_nodes'] for x in routes]}))

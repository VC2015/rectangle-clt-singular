import hashlib,json,pathlib,datetime
R=pathlib.Path(__file__).resolve().parents[2];O=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
exports=[O/'checkpoint-1/expanded-types.json',O/'support-checkpoint-1/expanded-types.json'];G={};E={}
for p in exports:
 d=json.loads(p.read_text())
 for x in d['project_dependency_graph']:
  if x['name'] in G:assert G[x['name']]==x['direct_project_dependencies']
  G[x['name']]=x['direct_project_dependencies']
 for x in d['endpoints']:
  if x['name'] in E:assert E[x['name']]==x
  E[x['name']]=x
A='RectangleCLT.Companion.SplitV4.';P=A+'Printed.';N='RectangleCLTArxivV1.'
def closure(n):
 s=set();q=[n]
 while q:
  x=q.pop()
  if x in s:continue
  s.add(x);q+=G.get(x,[])
 return s
routes=[
 (N+'lemma_1_bounded_model',[P+'bounded_intrinsic_boundary_fixed_shift_printed',A+'uniformCubeSelectedSum_test_transport',A+'cubePairIntrinsicBudget_eq_half_copy',A+'cubePairIntrinsicBudget_le_norm_sum',P+'cube_translated_boundary_printed',A+'finiteMaximum_pair_contraction',A+'cube_average_contraction',A+'cube_square_contraction_intrinsic',A+'independent_square_sum_fluctuation_le',A+'probability_bad_rows_le_norm_fluctuation',A+'cube_pair_bad_variance_probability_le','RectangleCLT.BoundedIndependentHypotheses.integral_norm_sum_le_of_variance']),
 (N+'lemma_C1_gaussian_model',[P+'intrinsicGaussianBoundary_printed_mollification',P+'gaussianMollifiedRamp_deriv_tendsto',A+'smoothGaussianFaceMaximum_stein',A+'smoothGaussianFaceHessian_trace_nonneg',A+'gaussian_affine_branches_ae_distinct_rows_ne',A+'smoothGaussianFaceGradient_normSq_tendsto_one',A+'gaussianAffineMaximum_level_zero',A+'integral_positiveGaussianFaceMaximum_le_sqrt_log',N+'gaussianIntrinsicBoundary_independent_shift']),
 (N+'corollary_1_normalized_observations',[N+'normalizedObservationsIntrinsicCLT',N+'boundedIndependent_normalizedObservationArray',N+'covariance_normalizedObservationArray_diagonal',N+'sum_normalizedObservationArray',N+'normalized_intrinsic_envelope_rate',N+'intrinsicEnvelopeCLT']),
 (N+'lemma_2_smoothing_error',[N+'intrinsicRectangleConcentration_bounded_endpoint',N+'intrinsicRectangleConcentration_gaussian_endpoint',N+'endpoint_error_le_intrinsic_average_radius',P+'endpoint_error_le_average_radius',P+'random_rectangle_sandwich',P+'endpoint_probability_bound','RectangleCLT.FaceSmoother.integral_F_eq_randomRectangle_average',P+'exponential_pair_upper_tail',P+'exponential_pair_lower_tail',P+'exponential_pair_abs_log_ratio_tail',P+'clock_abs_log_ratio_tail',P+'clockLogMaximum_tail_le',P+'integral_le_log_add_one_of_exponential_tail',P+'integral_randomThresholdRadius_le_log'])]
checks=[]
for n,req in routes:
 c=closure(n);missing=sorted(set(req)-c);assert not missing,(n,missing)
 checks.append({'endpoint':n,'closure_nodes':len(c),'required_actual_routes':req,'all_present':True})
for d in [json.loads((O/'checkpoint-1/run.json').read_text()),json.loads((O/'support-checkpoint-1/run.json').read_text())]:
 assert d['status']=='passed'
 for p,h in d['source_sha256'].items():assert sha(R/p)==h,p
out={'scope':'Actual proof-route check for early selected endpoints, derived from Lean kernel declaration values/types, not textual import reachability. No q0 derivative source correspondence claim.','status':'passed','generated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'export_sha256':{str(p.relative_to(R)):sha(p) for p in exports},'full_type_count':len(E),'dependency_nodes':len(G),'checks':checks}
(O/'dependency-check.json').write_text(json.dumps(out,indent=2)+'\n');(O/'expanded-types.json').write_text(json.dumps({'scope':out['scope'],'project_dependency_graph':[{'name':n,'direct_project_dependencies':v} for n,v in G.items()],'endpoints':list(E.values())},indent=2)+'\n');print(json.dumps({'status':out['status'],'full_type_count':len(E),'dependency_nodes':len(G),'checks':len(checks)}))

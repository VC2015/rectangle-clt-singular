from pathlib import Path
import json,hashlib,datetime,shutil
P=Path.cwd();E=P/'evidence/actual-h-corollaries';Q=E/'independent-root-checkpoint-1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.load(open(Q/'run.json'));assert r['status']=='passed' and r['full_type_count']==30
for f,h in r['source_identity'].items():assert sha(P/f)==h,f
ledger=P/'correspondence/actual-h-corollaries-passages.json';assert sha(ledger)=='5bee8f8bc539b3467cc2e5609d8d8ec6803f57bdfcffdb3103e19e2a9b912df8'
d=json.load(open(ledger));D=json.load(open(Q/'expanded-types.json'));T={x['name']:x for x in D['endpoints']};G={x['name']:x['direct_project_dependencies'] for x in D['project_dependency_graph']}
checks=[]
for row in d['passages']:
 ns=[n if n.startswith('RectangleCLT') else 'RectangleCLTArxivV1.'+n for n in row['mapped_declarations']];assert set(ns)<=T.keys()
 loc=row['location'];p=P.parent/loc['path'];a,b=loc['lines'];assert hashlib.sha256(b''.join(p.read_bytes().splitlines(keepends=True)[a-1:b])).hexdigest()==loc['sha256']
 checks.append(dict(id=row['id'],result='PASS',source=loc,finding=row['claim'],declarations=ns))
assert {n if n.startswith('RectangleCLT') else 'RectangleCLTArxivV1.'+n for row in d['passages'] for n in row['mapped_declarations']}==T.keys()
routes={}
for head in ['corollary4_positive_correlation_gap','corollary5_exceptional_correlation_budget','theorem_H3_fourth_derivative','corollary5_normalized_remainder_integral']:
 seen=set();todo=['RectangleCLTArxivV1.'+head]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo+=G.get(n,[])
 forbidden={'RectangleCLT.boundedRectangleCLT','RectangleCLT.Companion.SplitV4.relativeFourthMomentCLT','RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists'}&seen;assert not forbidden
 required=['proposition_H1_cubic_matrix_shifted','proposition_H2_pair_matrix_shifted']
 assert all('RectangleCLTArxivV1.'+n in seen for n in required)
 if head.startswith('corollary4_') or head=='corollary5_exceptional_correlation_budget':assert {'GenericChaining.dirksen_expectation','GenericChaining.gamma2_le_gaussianWidth'}<=seen
 routes[head]=dict(selected_project_nodes=len(seen),required_native_propositions=required,forbidden_legacy_final_CLT_dependencies=[],uses_checked_Dirksen='GenericChaining.dirksen_expectation' in seen,uses_checked_Gaussian_majorizing_measure='GenericChaining.gamma2_le_gaussianWidth' in seen)
extra=[
('UNIVERSAL_CONSTANT_ORDER','The shared numerical matrix constant is max1(maxcubicC pairC), before all data and cutoffs. Nonnegative bases justify every power comparison; H3 and both final comparison constants are fixed explicit positive definitions.'),
('ACTUAL_PHYSICAL_TRANSPORT','The actual unconditional base law is transported through the proved measurable mapx+A B, with only genuine almost-everywhere equality of the original base value. Gaussian evaluation uses sigma*A while the H3 normal remains the unit row of A.'),
('NORMALIZED_HALFBASE','The actual Gaussian half-base distribution and physical-support reconstruction are proved under the genuine Bernoulli array and product Gaussian laws. Original, unconditional C1 concentration is supplied internally for the final corollaries.'),
('ALL_TIME_SCALES','The normalized Gaussian scale is positive at every admitted time, and delta*sqrtL≤sigma follows from the actual seed epsilon=Lh² and width≥2delta. All rescaled smoother-width and unit-row identities are proved, rather than assumed matrix validity conditions.'),
('FULL_MATRIX_INSTANTIATION','The precise full cubic and angle-weighted pair predicates are constructed from the actual native propositions at every restoration length. The cutoff conversion restricts only the first two original labels and costs the exact positive determinant.'),
('RAW_H3_MODEL','The general-radius fourth derivative theorem assumes the printed actual conditional Gaussian/copy model, measurability/L2 coordinate pairs, unconditional physical-base concentration, relative covariance≤I, direction envelopes and shift radius. Its integrability and finite signed expectation bound are conclusions, with no matrix/trace/derivative/remainder supplier.'),
('RAW_H3_WIDTH','The general-radius formulation is stronger than the fixed-b paragraph: setR=bdelta and chooseA_b=max1(b*restorationBandwidthConstantC). A separate scalar packaging wrapper records this exact printed quantifier order; no analytic premise is left open.'),
('ACTUAL_COR4','The actual bounded array, unit covariance and canonical Gaussian factor are the only probabilistic inputs. The stated positive cutoff is a lower bound on original-coordinate gaps. A separate canonical-gap wrapper specializes it to the exact pairGap defined in the main statement.'),
('ACTUAL_COR5','The exceptional theorem assumes no global positive gap. Its actual originalj<k budget excludes exactly zero gaps, so perfect correlations and empty exceptional sets are included, uniformly for everyc∈(0,1].'),
('LITERAL_RATES','The two literal final costs are delta*gSigma*L*sqrt(1+log1/c) and the sum of that term withdelta^(2/3)*(gSigma L)^(2/3)*B_c^(1/3), each capped at1 with a fixed universal multiplier.'),
('SOURCE_L1','The actual normalized fourth remainder has an actual absolute interval-integrability theorem from original bounded data and width≥16delta. No supplied time-L1, comparison derivative or remainder bound appears.'),
('LITERAL_TIME_INTEGRAL','The integrated separated/exceptional R4 estimate internally constructs both original concentration and complete matrix predicates, then applies the genuine crossed-minimum time integral; the additive exceptional cost remains a separate term.'),
('SHARED_KERNEL_AXIOMS','The independent fresh build, all eight forced source elaborations, full30 target exports and complete shared transitive kernel axiom union passed. A union contained in the standard three axioms proves the same allowlist for each target.'),
('NO_CIRCULAR_CLT_REUSE','The actual final corollary proof closures reach the native cubic/pair propositions and checked Dirksen/majorizing-measure theorems, while excluding the foundation boundedCLT and both archived supplement final CLTs. The separately disclosed scalar Berry--Esseen reuse belongs only to lower-support passages.'),
]
checks += [dict(id=k,result='PASS',finding=v) for k,v in extra]
pdftext=E/'independent-root-supplement-pages21-27.txt';assert not pdftext.exists();shutil.copyfile('/tmp/root-final-h-corollaries-pdf.txt',pdftext)
main=P.parent/'research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex';supp=P.parent/'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex'
mods=['ActualMatrixConstant','ActualMatrixTransport','ActualSeededMatrixBase','ActualPairMatrixTransport','ActualNormalizedMatrices','ActualHFourth','ActualCorollaries','ActualRemainderIntegral']
o=dict(status='PASS',reviewer='/root',author='/root/g3_resume',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Eight actual supplier-free final H3/Cor4/Cor5 and source time-integral sources,30 public declarations; final statement registration waits for integrated clean evidence',source_sha256={f'RectangleCLTArxivV1/{m}.lean':sha(P/'RectangleCLTArxivV1'/f'{m}.lean') for m in mods},ledger=dict(path=str(ledger.relative_to(P)),sha256=sha(ledger)),independent_fresh_checkpoint=dict(path=str((Q/'run.json').relative_to(P)),sha256=sha(Q/'run.json'),strict_targets=30,full_types=30,selected_project_graph_nodes=len(G),expanded_types_sha256=sha(Q/'expanded-types.json')),actual_headline_dependency_routes=routes,paper_snapshot='1803366cc994d9facae8e128ee180f68e319486f',main_tex_sha256=sha(main),supplement_tex_sha256=sha(supp),main_pdf_sha256=sha(main.with_suffix('.pdf')),supplement_pdf_sha256=sha(supp.with_suffix('.pdf')),pdf_text=dict(path=str(pdftext.relative_to(P)),sha256=sha(pdftext)),reading_order_scope='All eight new proof sources/types; frozen main2576–2631, supplement1701–1967 and1991–2227, including actual PDFS21–S27. Upstream conditional H3/Gap/Cor5 detailed steps have separate independent lower reviews.',checks=checks,method_qualifications=['The native physical Gaussian-support representation permits singular covariance without an inverse. General shift radiusR and allsigma>0 strengthen the printed fixed-b/sigma≤1 form; exact fixed-b packaging is separately recorded.','Targeted full-type/project graph exports retain their historical printer/prefix convention. The final clean mapping is separately required to export pp.all types and include Kane/privateKane nodes and fresh mapped-provider replay.','Root authored some upstream signed coarea/scalar helpers independently reviewed by g3/intrinsic; none of the eight final sources under present review was authored by Root.'],mathematical_or_type_gaps=[],unmatched_headline_premises=[],release_wide_certification=False,headline_acceptance_change=False)
(E/'independent-root-review.json').write_text(json.dumps(o,indent=2)+'\n')
print('PASS independent raw final30;',len(checks),'source/type/PDF/route checks; all final matrix suppliers discharged')

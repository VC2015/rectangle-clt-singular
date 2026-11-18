from pathlib import Path
import json,hashlib,datetime
P=Path.cwd(); E=P/'evidence/supplement-h-pair-cross-review'; Q=E/'independent-root-checkpoint-1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
run=json.load(open(Q/'run.json')); assert run['status']=='passed' and run['full_type_count']==39
D=json.load(open(Q/'expanded-types.json')); types={r['name']:r for r in D['endpoints']}
modules=['SupplementalHPairPlane','SupplementalHPairSelectorReference','SupplementalHPairFamilyReference','SupplementalHPairFamilyEntropy','SupplementalHPairAveragingKernels','SupplementalHPairExtraFactors','SupplementalHPairMatrixAssembly','SupplementalHPairConstant']
for f,h in run['source_identity'].items():assert sha(P/f)==h,f
main=P.parent/'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex'; lines=main.read_bytes().splitlines(keepends=True)
ledgers=['supplemental-h-pair-projected-reference-passages.json','supplemental-h-pair-family-support-passages.json','supplemental-h-pair-assembly-support-passages.json']
checks=[]
for name in ledgers:
 path=P/'correspondence'/name; d=json.load(open(path))
 for row in d['passages']:
  lo,hi=row['location']['lines'];assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()==row['location']['sha256']
  names=[n if n.startswith('RectangleCLT') else 'RectangleCLTArxivV1.'+n for n in row['mapped_declarations']];assert set(names)<=types.keys(),set(names)-types.keys()
  checks.append(dict(id=row['id'],result='PASS',source_lines=[lo,hi],finding=row['claim'],declarations=names))
extra=[
('ACTUAL_PROJECTION','The constructed rank-one sum is genuinely symmetric/idempotent and fixes both original normal coordinates, with the exact two-coordinate norm-square formula. The nonparallel condition is explicit; no ambient inverse is used.'),
('REFERENCE_DOMINATION','The actual two-score reference denominator is bounded by the full smoother denominator; inactive faces give zero selector weights. Products of every later selector factor are bounded by1 after retaining the original tuple.'),
('REFERENCE_LAW','The actual reference kernel is measurable/L1 under the arbitrary outer law and Gaussian law. The previously independently checked native rank-two transport and exact two-score integral1/2 give2pi C0h²κ/sigma for each angle-weighted reference.'),
('ZERO_ANGLES','If rho² is not strictly below1, the Gram square root and angle factor vanish; every weighted mass, entropy, projection, trace and nuclear term is treated as zero. No singular plane reduction is applied in that branch.'),
('OUTER_ENTROPY','The same angle multiplies actual mass and reference mass before the true integral log-sum bound. Both share h²κ/sigma, so that scale cancels inside the logarithm. The zero-mass case uses the genuine entropy convention and integrability, with no log angle or log bandwidth cost.'),
('GENUINE_L1','The signed radial kernel is dominated by the actual Gaussian absolute radial score; projected energy by a finite sum of square Gaussian coordinates; bounded selector/reference kernels are dominated by1. Product Fubini proves actual outer L1 and measurable parameter integrals.'),
('MATRIX_ASSEMBLY','The pointwise actual weighted H2 score reduction is exactly2projection+4entropy−signedtrace; all finite sums and outer integrals are justified by the proved L1 assertions. Mass/projection/signed-trace budgets remain explicit ordinary-kernel premises in this supporting intermediate, rather than assumed target matrix or CLT conclusions.'),
('SCALAR_ABSORPTION','The nonnegative pair budget2D1+4(D0+2piC0)(K+3)+2^K D2 is absorbed into the explicit fixed base to powerK+3 using the separately independently reviewed Root scalar lemma. The constant is independent of process, dimension and tuple.'),
]
checks += [dict(id=k,result='PASS',finding=v) for k,v in extra]
pdf=P.parent/'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.pdf'
out=dict(status='PASS',reviewer='/root',author='/root/intrinsic_main',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Independent eight-source pair support review: actual plane/reference14, family/entropy16 and conditional ordinary-kernel assembly9; final supplier-free pair theorem is a separate obligation',source_sha256={f'RectangleCLTArxivV1/{m}.lean':sha(P/'RectangleCLTArxivV1'/f'{m}.lean') for m in modules},ledger_sha256={f'correspondence/{l}':sha(P/'correspondence'/l) for l in ledgers},independent_fresh_checkpoint=dict(path=str((Q/'run.json').relative_to(P)),sha256=sha(Q/'run.json'),strict_targets=39,full_types=39,project_dependency_nodes=len(D['project_dependency_graph']),expanded_types_sha256=sha(Q/'expanded-types.json')),supplement_tex_sha256=sha(main),supplement_pdf_sha256=sha(pdf),paper_snapshot='1803366cc994d9facae8e128ee180f68e319486f',reading_order_scope='Frozen supplement1542–1667 and the actual cited matrix reduction/reference primitives; read all eight Lean sources and exact expanded types in dependency order',checks=checks,method_qualifications=['The reference density bound uses the actual checked one-coordinate Gaussian projection/concentration profile and exact pair-reference Fubini route instead of the printed annular marginal-density partition. This route was disclosed and independently checked in the upstream projected-reference packet.','This review does not claim independence for my upstream pair-reference/scalar helper authorship; their separate intrinsic/g3 independent reviews remain binding evidence. None of the eight sources under present review was authored by Root.'],mathematical_or_type_gaps=[],unmatched_headline_premises=[],headline_acceptance_change=False,release_wide_certification=False)
(E/'independent-root-review.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS pair support independent Root39 strict/fulltypes;',len(checks),'source/type/method checks')

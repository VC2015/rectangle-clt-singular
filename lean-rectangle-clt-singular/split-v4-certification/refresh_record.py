#!/usr/bin/env python3
"""Derive the current correspondence/receipt from successful frozen evidence."""
import argparse, collections, datetime, hashlib, json, re, subprocess
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('--logs',required=True)
ap.add_argument('--closure-log',required=True)
ap.add_argument('--extra',action='append',default=[])
ap.add_argument('--validate-only',action='store_true')
args=ap.parse_args()
cert=Path(__file__).resolve().parent; pkg=cert.parent; repo=pkg.parent
logs=Path(args.logs).resolve(); run=json.loads((logs/'run.json').read_text())
assert run['required_commands_passed'] and run['exit_code']==0
assert not run.get('inputs_changed_during_run') and not run.get('dependency_revision_mismatches')
assert all(c['exit_code']==0 for c in run['commands'])
proof=run['before']['git_commit']; cmds={c['name']:c for c in run['commands']}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rel=lambda p:str(Path(p).resolve().relative_to(repo))
local=lambda p:str(Path(p).resolve().relative_to(pkg))
dump=lambda p,d:None if args.validate_only else Path(p).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def logfile(name): return logs/cmds[name]['log']
for c in cmds.values(): assert sha(logs/c['log'])==c['log_sha256']
for path,digest in run['before']['sources_sha256'].items():
    data=subprocess.check_output(['git','show',f'{proof}:{path}'],cwd=repo)
    assert hashlib.sha256(data).hexdigest()==digest,path

def extract(path):
    result={}; lines={}; count=0
    for no,line in enumerate(path.read_text().splitlines(),1):
        pos=line.find('SPLITV4_DEPENDENCY ')
        if pos<0: continue
        # Fresh direct Lean output is plain JSON; Lake --json wraps and escapes messages.
        if line.startswith('{'):
            try:
                obj=json.loads(line)
                if 'message' in obj: line=str(obj['message'])
            except json.JSONDecodeError: pass
            pos=line.find('SPLITV4_DEPENDENCY ')
        try:d=json.loads(line[pos+len('SPLITV4_DEPENDENCY '):])
        except json.JSONDecodeError:continue
        key=d['declaration']; count+=1
        assert key not in result or result[key]==d
        assert set(d['transitive_axioms'])<= {'propext','Classical.choice','Quot.sound'}
        result[key]=d;lines.setdefault(key,[]).append(no)
    assert result
    return result,lines,count

records,recordlines,rawcount=extract(logfile('DependencyAudit'))
buildrecords,_,_=extract(logfile('split-v4-build'))
assert records==buildrecords,'Fresh build and direct dependency outputs differ'
newthms=[d for d in records.values() if d['module'].startswith('RectangleCLTCompanion.SplitV4.') and d.get('declaration_kind','theorem')=='theorem']
constructors=[d for d in records.values() if d.get('declaration_kind')=='definition']
old=[d for d in records.values() if not d['module'].startswith('RectangleCLTCompanion.SplitV4.')]
modules=collections.Counter(d['module'] for d in records.values())
closure=Path(args.closure_log).resolve();cm=re.search(r'Audited (\d+) companion theorem declarations',closure.read_text());assert cm
closure_count=int(cm[1]); assert closure_count >= len(newthms)
audit=logfile('Audit'); audittext=audit.read_text()
am=re.search(r'Audited (\d+) split-V4 checkpoint',audittext);assert am

dep=json.loads((cert/'checkpoints/fad0623/dependency-map.json').read_text())
dep.update(proof_commit=proof,scope=f'{len(records)} selected kernel-checked declarations: {len(newthms)} new theorem declarations, {len(constructors)} explicitly checked C4 constructors, and {len(old)} historical endpoints. This is a partial manuscript checkpoint.',declarations=sorted(records.values(),key=lambda d:d['declaration']))
dep['axiom_policy']['observed_union']=sorted({a for d in records.values() for a in d['transitive_axioms']})
dep['extraction'].update(source=rel(logfile('DependencyAudit')),source_sha256=sha(logfile('DependencyAudit')),build_crosscheck=rel(logfile('split-v4-build')),build_crosscheck_sha256=sha(logfile('split-v4-build')),all_records_identical_across_build_and_direct_audit=True,deduplicated_record_count=len(records),raw_direct_record_count=rawcount)
edgecount=sum(len(d[k]) for d in records.values() for k in ['type_used_constants','value_used_constants'])
inside=sum(n in records for d in records.values() for k in ['type_used_constants','value_used_constants'] for n in d[k])
dep['validation'].update(build_command_exit_code=0,split_v4_build_command_exit_code=0,direct_dependency_audit_exit_code=0,direct_statement_audit_exit_code=0,command_record=rel(logs/'run.json'),selected_declarations=len(records),modules=dict(sorted(modules.items())),direct_typed_edges=edgecount,edges_to_selected_declarations=inside,edges_to_external_declarations=edgecount-inside)

statement=json.loads((cert/'checkpoints/fad0623/statement-map.json').read_text())
ns='RectangleCLT.Companion.SplitV4.'
completed={
 'ben:smoothing':ns+'gaussianEndpointSmoothing',
 'ben:maximum':ns+'truncated_bennett_maximum',
 'ben:paired-interpolation':ns+'C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths',
 'lem:maximum':ns+'expected_maximum_under_envelope_moment',
}
completed.update({label:ns+name for label,name in {
 'ben:comparison':'gaussianComparisonWithLargeIncrementRemainders',
 'lower:shift-comparison':'independent_shift_comparison',
 'appx-lem:cube-boundary':'intrinsic_cube_boundary',
 'poly:transfer':'polynomialEnvelopeTransfer',
 'poly:bennett':'bennettPolynomialCLT_observations',
 'thm:polynomial':'polynomialMomentCLTExists',
 'lower:family-properties':'symmetricFamilyProperties',
 'lem:concentration':'lemma_concentration',
 'opt:moderate-tail':'uniformScalarModerateTail',
 'appx-an:lem:threshold':'averagedGaussianThresholdDerivative_rectangle_bound',
 'opt:symmetric-lower':'boundedSymmetricLower',
 'appx-an:lem:matrix':'exists_logistic_matrix_paper_constant',
 'opt:q4-lower':('fourthMoment_uniform_constants' if ns+'fourthMoment_uniform_constants' in records else 'fourthMomentOptimal'),
 'appx-an:lem:restoration':'lemma_paired_restoration',
 'lower:dense':('denseMoment_uniform_constants' if ns+'denseMoment_uniform_constants' in records else 'denseMomentOptimal'),
 'lower:sparse':'sparseMoment_uniform_constants',
 'appx-an:lem:identity':'hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor',
 'opt:q4-growing':'maskedFourthLower',
 'appx-lem:envelope':'lemma_derivative_envelope',
}.items() if ns+name in records})
completed.update(x.split('=',1) for x in args.extra)
for label,name in completed.items():assert name in records,(label,name)

def evidence(name):return {'proof_commit':proof,'dependency_map':rel(cert/'dependency-map.json'),'declaration_key':name,'log':rel(logfile('DependencyAudit')),'lines':recordlines[name]}
def attach(item,key='declaration'):
    name=item.get(key)
    if name in records:
        d=records[name]
        item.update(expanded_lean_type=d['expanded_lean_type'],expanded_type_status='actual_elaborated_type_from_successful_dependency_audit',transitive_axioms=d['transitive_axioms'],axiom_audit_status='passed_only_permitted_axioms',fresh_evidence=evidence(name))

# Recover the actual printed definitions, keeping the source text and proof types separate.
definition_starts=[]
auditlines=audittext.splitlines()
for i,line in enumerate(auditlines):
    m=re.match(r'^(def|structure|class|inductive|abbrev)\s+(\S+)',line)
    if m:definition_starts.append((i,m[1],m[2].split('.{')[0]))
definitions={}
for idx,(start,kind,name) in enumerate(definition_starts):
    end=definition_starts[idx+1][0] if idx+1<len(definition_starts) else len(auditlines)
    for j in range(start+1,end):
        if auditlines[j].startswith('RectangleCLT.') and ':' in auditlines[j]:end=j;break
    definitions[name]={'name':name,'print_kind':kind,'printed_definition_or_structure':'\n'.join(auditlines[start:end]).strip(),'log':rel(audit),'log_sha256':sha(audit),'line_start':start+1,'line_end':end,'proof_commit':proof}

helper_modules={
 'ben:smoothing':['ClockCutoff','GaussianEndpointSmoothing'],
 'ben:maximum':['BennettTruncation','BennettMaximum'],
 'lem:maximum':['EnvelopeTruncation','EnvelopeMaximum'],
 'ben:paired-interpolation':['PairedSlepian','MomentIntegrability','CopyProjection','SlepianDerivative','ProductConditional','PairedCoefficients','ArraySlepian'],
 'ben:comparison':['SmootherC4','CommonPointFourth','CommonPointGaussianAverage','FourthMaximum','PairedMoments','ConditionalMatrixFluctuation','PairedTailBudgets','GaussianDerivativeContractions','GaussianRemainder','LargeIncrementBudgets','LargeIncrementComparison','PairedNormalization'],
 'poly:bennett':['BennettTruncation','BennettMaximum','PairedMoments','BennettPolynomial','BennettOptimization'],
 'poly:transfer':['ConditionalTruncation','ConditionalTruncationKernel','EnvelopeMaximum','UnrestrictedGaussianComparison','ConditionalTruncationBounds','ConditionalPolynomial'],
 'cor:polyhedral-transfer':['GaussianFaceTransfer','OrliczFaceTransfer'],
 'lower:shift-comparison':['ShiftComparison'],
 'lem:concentration':['IntrinsicVariance','CubeContraction','CubeCopySelection','BoundedIntrinsicConcentration','BoundedFaceIntrinsicConcentration','IntrinsicGaussianBoundary','GaussianIntrinsicConcentration','Concentration'],
 'appx-lem:cube-boundary':['IntrinsicCubeData','IntrinsicCubeMaximum','IntrinsicCubeBoundary'],
 'opt:moderate-tail':['ModerateCumulants','ModerateTiltBounds','ModerateFourthCumulant','ModerateArrayCumulants','ModerateInverse','ModerateInverseTilt','ModerateProductCumulants','ModerateSmallThreshold','ModerateProductTail','ModerateTail','ModerateTailGeneral','GenericProductTilt'],
 'lower:family-properties':['SymmetricFamilyFinite','SymmetricFamily','SymmetricFamilyMoments','SymmetricFamilyProperties','SymmetricFamilyGeometry','SymmetricFamilyEnvelope','SymmetricFamilyCertification'],
 'thm:polynomial':['PolynomialUniform','PolynomialMain'],
 'appx-an:lem:identity':['SeededInterpolation','VariableAmplitudeInterpolation'],
 'thm:unrestricted':['RelativeFourthRefinement','RelativeMoments','SeedCalibration'],
}
helper_modules.update({
 'appx-an:lem:threshold':['AveragedThresholdBound','AveragedThresholdCoarea','GaussianThresholdPairCoarea','GaussianThresholdPairTubes','GaussianThresholdTubes','GaussianThresholdIdentity','GaussianRadialScaling'],
 'opt:symmetric-lower':['SymmetricBoundedLower','SymmetricBoundedCalibration','SymmetricBoundedRemainder','SymmetricBoundedFamily','ModerateTailGeneral','LowerCalibrationScales'],
 'appx-an:lem:matrix':['LogisticMatrixPaper','LogisticMatrixRegularizedBound','LogisticMatrixRegularized','LogisticMatrixRegularization','LogisticMatrixPadding','LogisticGammaTrace','LogisticLimits','NuclearTraceDual'],
 'opt:q4-lower':['FourthMomentFamily','FourthMomentCalibration','FourthMomentLower','FourthMomentOptimal','UniformLowerConstants','FourthLowerCalibrationScales','SymmetricPolynomialUniform'],
 'lower:sparse':['SparseFamily','SparseFamilyMoments','SparseFamilyCalibration','SparseMomentLower','SparseMomentOptimal','SparseUniformBounds','UniformLowerConstants','SparseLowerLogScales','SparseLowerPaperRate','SparseCoordinateNegligible','SparseLowerCalibrationScales','SparseLowerCalibrationLimits','SparseMaskLogAsymptotics'],
 'opt:q4-growing':['MaskedFourthFamily','MaskedFourthCalibration','MaskedFourthLower','MaskedFourthLowerCalibrationScales','RareFamilyComparison'],
 'lower:dense':['DenseMomentFamily','DenseMomentCalibration','DenseMomentLower','DenseMomentOptimal','UniformLowerConstants','DenseLowerCalibrationScales','SymmetricFamilyPolynomial'],
 'appx-an:lem:restoration':['Restoration','RestorationConditionalTransport','ConditionalGaussianTransport','NuclearSelectorMatrixInterface','RestorationProductBounds','RestorationPairedBounds'],
 'appx-an:lem:identity':['GenericC4CubicTensor','GenericC4SeededFourthIdentity','GenericC4FourthIdentity','GenericC4OuterFourth','GenericC4CubicLaw','GenericC4Symmetry','GenericC4Heat','GenericC4FourthIntegral','VariableAmplitudeFourthIdentity','VariableAmplitudeRowTaylor'],
 'appx-lem:envelope':['DerivativeEnvelopeAllOrders','LogisticScalarJets','LogisticDerivativeEnvelope','LogisticDerivativeFaceEnvelope','DerivativeEnvelopeAverage','DerivativeEnvelopeAverage34','DerivativeEnvelopeStability','DerivativeEnvelopeSupremum','DerivativeEnvelopeModels'],
})
newdefinitions={
 'ben:smoothing':['gaussianSmoothingConstant','smoothingDiscrepancy'],
 'ben:paired-interpolation':['C4Test','C4Test.ofContDiff','copyArrayLargeMean','copyArrayTruncatedCovariance','originalSigma','productArrayLargeMean','productArrayTruncatedCovariance'],
 'ben:maximum':['bennettTruncate'],
 'lem:maximum':['envelopeMaximumConstant'],
 'lower:shift-comparison':['realCDF','realCDFDistance','secondDerivativeSupNorm'],
 'ben:comparison':['largeIncrementMasterConstant','largeIncrementMasterRate','normalizedSummands','deltaOne','pairedTailVariance','pairedTailExpectedMaximum'],
 'thm:polynomial':['PolynomialIndependentHypotheses','polynomialClassDistances','polynomialWorstDistance','PolynomialModelBound','polynomialBennettObservationRate','polynomialEnvelopeTransferRate','polynomialCombinedRate','polynomialUniversalConstant'],
 'lower:family-properties':['SymmetricFamilyParameters','SymmetricFamilyParameters.variance','SymmetricFamilyParameters.scale','familySeedLaw','familyArrayLaw','familyObservation','familyRawObservations','CommonSymmetricFamilyProperties'],
 'lem:concentration':['BoundedConcentrationContract','GaussianConcentrationContract'],
 'opt:moderate-tail':['moderateArrayCGF','moderateArrayGamma','moderateScalarSum'],
 'appx-lem:cube-boundary':['cubeUniformLaw','affineCubeMaximum','positiveLinearMaximum','intrinsicCubeMean'],
}
newdefinitions.update({
 'appx-an:lem:threshold':['ConcentratedThresholdBase'],
 'opt:symmetric-lower':['BoundedSymmetricLowerConstruction'],
 'appx-an:lem:matrix':['PolyhedralBaseConcentration'],
 'appx-an:lem:identity':['signedCubicTensor','canonicalSignedCubicContraction','variableRetention','variableEta','variableSeededInterpolationLaw','genericManuscriptFourthCombination','genericManuscriptFourthPathIntegrand'],
 'appx-an:lem:restoration':['restorationOriginalThird','restorationOriginalFourth','PairedRestorationConclusion','PairedRestorationContract','ConditionalEventIndependence','conditionalRestorationCoefficient','RectangleBaseConcentration'],
 'appx-lem:envelope':['DerivativeEnvelopeComponent','translatedFaceDerivativeSupremum','DerivativeEnvelopeAverageContract'],
 'opt:q4-growing':['MaskedFourthLowerConstruction'],
 'lower:sparse':['SparseMomentLowerConstruction','sparseMomentK','sparseMomentLowerRate','sparseMomentLowerCoefficient','sparseMomentUpperCoefficient'],
 'opt:q4-lower':['FourthMomentLowerConstruction','polynomialSymmetricClassDistances','polynomialSymmetricWorstDistance','polynomialFourthUniformConstant'],
 'lower:dense':['DenseMomentLowerConstruction','polynomialSymmetricClassDistances','polynomialSymmetricWorstDistance'],
})
for e in statement['entries']:

    label=e['label']
    if label in completed:
        name=completed[label];d=records[name]
        e.update(current_statement_status='proved_and_freshly_checked',current_proof_route_status='proved_current_route',lean_declaration=name,expanded_lean_type=d['expanded_lean_type'],expanded_lean_type_status='actual_elaborated_type_from_successful_dependency_audit',minimal_open_obligations=[],transitive_axioms=d['transitive_axioms'])
        e['certification_evidence']={'fresh_build_log':rel(logfile('split-v4-build')),'fresh_type_log':rel(logfile('DependencyAudit')),'fresh_axiom_log':rel(logfile('DependencyAudit')),'proof_commit':proof}
        e['fresh_evidence']=evidence(name)
        if label=='ben:smoothing':
            e['current_proof_route_status']='proved_gaussian_endpoint_absorption_with_clock_cutoff_variant'
            e['notes']='Arbitrary measurable V, no moment/boundedness premise; unit marginal Gaussian factor may be singular. Actual mixture, good-clock cutoff, Gaussian shells and full-distance absorption. The deterministic cutoff replaces the printed expected-clock-width step.'
        if label=='ben:paired-interpolation':e['notes']='Apply to normalized observations ξ_i=X_i/sqrt(n). The endpoint is valid for arbitrary Gaussian factor A, in particular the exact covariance factor. Actual copy integrals are proved equal to conditional expectations given the original observation-generated sigma-field. The ordinary C4 constructor supplies genuine derivative witnesses; no symmetry or zero-skewness premise.'
        if label=='lem:maximum':e['notes']='Follows the centered truncation/Bernstein proof, with explicit universal constant 4+2 exp(1), stronger than q-dependent constants. Includes A=0 and v=0; A is a nonnegative moment scale and all moments are genuine integrability contracts.'
        if label=='appx-lem:cube-boundary':
            e['current_proof_route_status']='proved_direct_tie_safe_supporting_branch_route'
            e['notes']='Actual uniform-cube probability and intrinsic positive maximum. Direct selected supporting branches handle ties and zero coefficients; the separate logarithmic specialization is also proved.'
        if label=='opt:moderate-tail':e['notes']='Arbitrary independent, nonidentically distributed centered bounded scalar laws with variance sum one. Absolute constants precede all models, the tail is strict and proved positive including atoms at zero; genuine tilted laws and integrability are established.'
        if label=='ben:maximum':e['notes']='Actual Bennett MGF/product/log-sum-exp proof; universal constant 2, exact omitted-tail coefficient 1, every q>1, plus actual a.e. zero at v=0.'
    name=e.get('lean_declaration')
    if name in records:
        e['expanded_lean_type']=records[name]['expanded_lean_type'];e['fresh_evidence']=evidence(name)
        e['expanded_lean_type_status']='actual_elaborated_type_from_successful_dependency_audit'
        if e.get('current_statement_status')=='proved_and_freshly_checked':e['certification_evidence']={'fresh_build_log':rel(logfile('split-v4-build')),'fresh_type_log':rel(logfile('DependencyAudit')),'fresh_axiom_log':rel(logfile('DependencyAudit')),'proof_commit':proof}
    for candidate in e.get('reuse_candidates',[]):attach(candidate)
    olddefs=e.get('definition_expansion_evidence',[])
    names=list(dict.fromkeys([d['name'] for d in olddefs]+[ns+n for n in newdefinitions.get(label,[])]))
    if names:e['definition_expansion_evidence']=[definitions[n] for n in names if n in definitions]
    helpers=[]
    for mod in helper_modules.get(label,[]):
        module='RectangleCLTCompanion.SplitV4.'+mod
        ds=[d['declaration'] for d in records.values() if d['module']==module]
        if not ds:continue
        helpers.append({'module':module,'file':'lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/'+mod+'.lean','status':'kernel_checked_and_strict_axiom_audit_passed','declarations':sorted(ds),'proof_commit':proof,'dependency_map':rel(cert/'dependency-map.json'),'scope_limitation':'This certifies the actual elaborated declarations; whole-statement and proof-route status are separate fields.'})
    if helpers:e['checked_helper_modules']=helpers
    # Preserve older analytic-route evidence while removing stale references to completed inputs.
    if label=='appx-an:lem:identity' and label not in completed and any(d['module']=='RectangleCLTCompanion.SplitV4.SeededInterpolation' for d in records.values()):e['minimal_open_obligations']=['Complete arbitrary-amplitude fourth-order restoration and the generic smooth bounded-derivative test class. The actual calibrated FaceSmoother seeded identity and arbitrary-amplitude finite-mask probability differentiation are checked inputs.']
    if label=='poly:transfer' and label not in completed:e['minimal_open_obligations']=['Numeric conditional covariance/tail bounds and threshold probability assembly; optimize the actual threshold estimate in both n regimes.','Preserve full rectangle distance, exact actual conditional laws, nonidentical arrays and singular covariance. The unrestricted Gaussian comparison and conditional reconstruction kernel are proved inputs.']
    if label=='cor:polyhedral-transfer' and 'thm:polynomial' in completed:e['minimal_open_obligations']=['Relative-moment polyhedral final bound remains dependent on Theorem 1. Gaussian pushforward, bounded, Orlicz and polynomial final branches, B -> J^2 B, and the exact zero-variance-face deletion are checked.']

for h in statement['additional_required_helpers']:
    if h['id']=='unrestricted_gaussian_comparison_E':h.update(status='proved_and_freshly_checked',declaration=ns+'unrestrictedGaussianComparison_of_marginal_lower_bound',evidence_module='RectangleCLTCompanion.SplitV4.UnrestrictedGaussianComparison',proof_commit=proof,remaining=None)
    if h['id']=='conditional_truncation_laws':h.update(status=('proved_and_assembled_in_Proposition_2' if 'poly:transfer' in completed else 'actual_conditional_laws_and_exceptional_data_kernel_checked_numeric_assembly_pending'),evidence_modules=['RectangleCLTCompanion.SplitV4.ConditionalTruncation','RectangleCLTCompanion.SplitV4.ConditionalTruncationKernel','RectangleCLTCompanion.SplitV4.ConditionalPolynomialOptimization'],proof_commit=proof)
    if h['id']=='paired_common_point_fourth_contraction':h.update(status='common_point_contraction_and_actual_independent_gaussian_averaging_checked',evidence_modules=['RectangleCLTCompanion.SplitV4.CommonPointFourth','RectangleCLTCompanion.SplitV4.CommonPointGaussianAverage'],proof_commit=proof,remaining='Assemble with actual derivative, conditional budgets and time integration for G.1.')

for h in statement['additional_required_helpers']:
    if h['id']=='coordinate_duplication' and ns+'rectangleDistance_duplicateCoordinates' in records:
        h.update(status='proved_and_freshly_checked',proof_commit=proof,evidence_module='RectangleCLTCompanion.SplitV4.CoordinateDuplication',remaining=None)
    if h['id']=='threshold_regularization' and 'appx-an:lem:matrix' in completed:
        h.update(status='proved_and_assembled_in_B4',proof_commit=proof,evidence_modules=['RectangleCLTCompanion.SplitV4.LogisticMatrixPaper','RectangleCLTCompanion.SplitV4.LogisticMatrixRegularizedBound','RectangleCLTCompanion.SplitV4.LogisticMatrixRegularization'],remaining=None)
    if h['id']=='calibrated_path_identities' and 'appx-an:lem:identity' in completed:
        h.update(status='proved_generic_C4_interpolation_and_calibration',proof_commit=proof,limitation='Assembly in Proposition 1 is a separate inventory target.',remaining=None)
    if h['id']=='relative_moment_matrices' and 'appx-an:lem:restoration' in completed:
        h.update(status='actual_relative_matrices_and_conditional_restoration_checked',proof_commit=proof,remaining='Final propagation and optimization in Proposition 1 and Theorem 1 remain separate inventory targets.')

if 'ben:comparison' in completed:
    for h in statement['additional_required_helpers']:
        if h['id'] in ['paired_common_point_fourth_contraction','paired_time_integrals']:
            h.update(status='checked_and_assembled_in_full_G1',proof_commit=proof,remaining=None,limitation='Does not by itself close the other manuscript proof routes.')

checked=[e for e in statement['entries'] if e.get('current_statement_status')=='proved_and_freshly_checked']; count=len(checked)
statement.update(proof_commit=proof,status=f'Fresh partial checkpoint: {count} whole current statements checked; {31-count} proved statements pending; Conjecture 1 excluded. The paper is not certified.',checked_whole_statements=count,pending_whole_statements=31-count,paper_certified=False)
statement['fresh_evidence_summary'].update(proof_commit=proof,build_log=rel(logfile('split-v4-build')),dependency_audit_log=rel(logfile('DependencyAudit')),statement_and_contract_audit_log=rel(audit),declaration_records=len(records),command_record=rel(logs/'run.json'))

receipt=json.loads((cert/'checkpoints/fad0623/SPLIT_V4_VERIFICATION.json').read_text())
receipt.update(recorded_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proof_commit=proof,proof_sources_match_commit=True,scope=f'{count} whole current statements (or exact equivalent formulations), historical envelope specialization, and checked proof components. {31-count} proved statements remain pending; the whole manuscript is not certified.')
receipt['statement_counts'].update(whole_statements_checked=count,whole_statements_pending=31-count)
receipt['checked_current_statements']=[{'label':e['label'],'number':e['number'],'kind':e['kind'],'declaration':e['lean_declaration']} for e in checked]
baseline=cert/'logs-ci-eighteen-statements/split-v4-baseline/run.json'
assert json.loads(baseline.read_text())['required_commands_passed']
receipt['fresh_baseline'].update(workflow_run_id=42398843876,record=local(baseline),record_sha256=sha(baseline))
receipt['fresh_checkpoint'].update(source_commit=proof,record=local(logs/'run.json'),record_sha256=sha(logs/'run.json'),required_commands_passed=True,zero_exit_code_commands=len(cmds),inputs_changed_during_run=False,full_package_build_passed=True,all_new_modules_and_audits_built=True)
receipt['axiom_policy'].update(dependency_records=len(records),new_theorem_declarations=len(newthms),checked_constructor_definitions=len(constructors),reused_endpoints=len(old),combined_audit_entries=int(am[1]))
receipt['complete_import_closure_audit'].update(cwd=cmds['build']['cwd'],theorem_declarations=closure_count,log=local(closure),log_sha256=sha(closure),exit_code=0,source_commit=proof)
receipt['proof_sources_sha256']=run['before']['sources_sha256']
receipt['frozen_october_verification_records_sha256']=run['before']['frozen_records_sha256']
receipt['manifest_and_toolchain_sha256']=run['before']['manifests_sha256']
receipt['dependency_revisions_and_state']=run['before']['dependencies']
receipt['completed_current_routes']=[e['label'] for e in checked if e.get('current_proof_route_status','').startswith('proved_')]
receipt['remaining_core_blockers']=[e['label']+': '+(e.get('title') or e['kind']+' '+e['number']) for e in statement['entries'] if e.get('in_scope') and e.get('current_statement_status')!='proved_and_freshly_checked']
receipt['metadata_note']='Receipt generated after the proof commit from an isolated detached checkout with separate project builds. Every recorded Lean source hash is checked against that commit. Later in-progress files and manuscripts are outside this receipt.'
dump(cert/'dependency-map.json',dep);dump(cert/'statement-map.json',statement)
receipt['artifact_sha256']={'statement-map.json':sha(cert/'statement-map.json'),'dependency-map.json':sha(cert/'dependency-map.json'),'OPEN_OBLIGATIONS.md':sha(cert/'OPEN_OBLIGATIONS.md')}
dump(pkg/'SPLIT_V4_VERIFICATION.json',receipt)
print(json.dumps({'proof_commit':proof,'checked':count,'pending':31-count,'records':len(records),'new_theorems':len(newthms),'constructors':len(constructors),'closure':closure_count,'commands':len(cmds)},indent=2))

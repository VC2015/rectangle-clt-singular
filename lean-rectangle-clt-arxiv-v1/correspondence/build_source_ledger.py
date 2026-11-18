#!/usr/bin/env python3
"""Build/check source identity without certifying mathematical correspondence.

All source bytes are read with git show at the frozen manuscript commit. The
original inventory and archived evidence are read-only inputs. --check validates
pinned file/span hashes and exclusions, and never upgrades a proof status.
"""
from __future__ import annotations
import argparse, hashlib, json, pathlib, re, subprocess

HERE = pathlib.Path(__file__).resolve().parent
PROJECT = HERE.parent
ROOT = PROJECT.parent
INVENTORY = PROJECT / 'inventory.json'
ARCHIVE = ROOT / 'lean-rectangle-clt-singular/split-v4-certification'
COVERAGE = ARCHIVE / 'printed-proof-extension/coverage.json'
OLD_STATEMENTS = ARCHIVE / 'statement-map.json'
ENV = re.compile(rb'\\begin\{(theorem|lemma|proposition|corollary|conjecture)\}.*?\\end\{\1\}', re.S)
LABEL = re.compile(rb'\\label\{([^}]+)\}')
PAPER_COMMIT = '1803366cc994d9facae8e128ee180f68e319486f'
SOURCE_HASHES = {'main':'e96aaf12ca782c94d70587f128b58a20d3ace8b31a8c324a3272b2b1d71677a2',
                 'supplement':'5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb'}

def digest(data): return hashlib.sha256(data).hexdigest()
def read_json(path): return json.loads(path.read_text())
def frozen(commit, path): return subprocess.check_output(['git','show',f'{commit}:{path}'],cwd=ROOT)
def span(data, lines):
    a,b=lines; chunks=data.splitlines(keepends=True)
    if not (1 <= a <= b <= len(chunks)): raise ValueError(f'invalid span {lines}')
    return b''.join(chunks[a-1:b])
def envs(data): return {lab.decode():m.group() for m in ENV.finditer(data) for lab in LABEL.findall(m.group())}
def sid(label): return 'S-' + re.sub(r'[^A-Za-z0-9]+','-',label).strip('-')

def inputs():
    inv=read_json(INVENTORY); raw={}
    if inv['snapshot'] != PAPER_COMMIT: raise ValueError('unexpected paper snapshot')
    if {k:v['sha256'] for k,v in inv['source_files'].items()} != SOURCE_HASHES: raise ValueError('unexpected paper source hashes')
    for key,src in inv['source_files'].items():
        data=frozen(inv['snapshot'],src['path'])
        if digest(data)!=src['sha256']: raise ValueError(f'pin mismatch: {key}')
        raw[key]=data
    cov=read_json(COVERAGE); old=read_json(OLD_STATEMENTS)
    old_pin=cov['frozen_manuscript']; old_data=frozen(old_pin['commit'],old_pin['path'])
    if digest(old_data)!=old_pin['sha256']: raise ValueError('archive manuscript pin mismatch')
    return inv,raw,cov,old,old_data

def location(inv,raw,key,lines):
    return {'source':key,'path':inv['source_files'][key]['path'],'lines':lines,
            'sha256':digest(span(raw[key],lines)),
            'source_url':f"{inv['repository']}/blob/{inv['snapshot']}/{inv['source_files'][key]['path']}#L{lines[0]}-L{lines[1]}"}

REUSE_NOTES={
 'thm:unrestricted':'Intrinsic Gaussian width replaces the worst-case square-root-log factor. Requires the new C.2 comparison, intrinsic boundary coefficient, and both relative fourth-moment matrices through the final split.',
 'cor:observations':'Normalization must preserve the new Gaussian-width coefficient and both normalized fourth-moment budgets, including all quantifiers.',
 'cor:subexponential':'Recheck capping and variance normalization with Gaussian width retained; the old logarithmic rate alone does not give the new rate.',
 'thm:polynomial':'Match parts (i) and (ii) separately, preserving the intrinsic width, Bennett regime and all envelope parameters.',
 'cor:polyhedral-transfer':'Match standardized projected coordinates and their Gaussian width; handle zero projected variances without assuming a nonsingular covariance.',
 'lem:concentration':'The new bounded and Gaussian statements explicitly retain expected face maxima before their logarithmic consequences.',
 'lem:endpoint':'Keep the printed intrinsic boundary coefficient kappa through smoothing; replacing it by square-root-log would weaken the target.',
 'an:prop:derivative':'Rebuild direct and seeded estimates with kappa and both fourth-moment matrices; inspect every order/range and seed denominator.',
 'opt:skew-lower':'Recalibrate the iid-coordinate construction to the new Gaussian-width normalization and the printed 1/(4e) liminf with B_n possibly varying.',
 'opt:symmetric-lower':'The theorem now requires a prescribed Gaussian-width profile across singular common-factor constructions. Reuse historical tail components, not the old theorem as a wrapper without calibration.',
 'opt:q4-lower':'New width-profile and matching upper/lower rate calibration must be proved for the actual symmetric distribution.',
 'opt:q4-growing':'Retain the growing envelope, logarithmic loss and prescribed width profile with the correct quantifier order.',
 'lower:dense':'Part (i) and the fixed-envelope q>4 qualification in part (ii) require separate width and moment verifications.',
 'lower:sparse':'Recheck sparse masks, growing K_n,q, logarithmic loss and prescribed Gaussian-width profile before comparing the paired upper rate.',
 'appx-lem:envelope':'The current statement explicitly restricts q to positive integers. Reuse the qualified archive proof only; retain the new coefficient kappa and h/rho ranges.',
 'appx-an:lem:identity':'Tensor interpolation is a reuse candidate after matching masks, independent copies, seed, gamma, q_3, eta and all three printed fourth-order kernels.',
 'appx-an:lem:restoration':'Retain the conditional Gaussian independence, covariance budget, translated bases and signed cubic/two fourth-moment refinements with kappa.',
 'appx-an:lem:mean':'The statement environment is byte-identical. Ambient Gaussian law, integrability, weight positivity and expanded Lean type still require an explicit checked wrapper/review.',
 'appx-an:lem:matrix':'Retain kappa and ordered face tuples; distinguish the printed potential/Hessian proof from any external Brascamp--Lieb implementation route.',
 'appx-an:lem:threshold':'The intrinsic kappa coefficient must survive sector/tail integration and all threshold/correlation degeneracies.',
 'appx-lem:cube-boundary':'The intrinsic expected maximum M is the principal output; the logarithmic consequence is secondary. Match the exact variance/envelope factors.',
 'lem:maximum':'Candidate reuse of the moment-envelope maximal inequality after checking q>2 and the printed log(ep) convention.',
 'ben:comparison':'The new master inequality has an explicit g_Sigma/sqrt(L) factor. Keep the actual large-increment remainders and singular covariance.',
 'ben:smoothing':'The Gaussian endpoint smoothing error is now h*g_Sigma*L. Recheck the exact endpoint and rectangle conventions.',
 'ben:paired-interpolation':'Match the conditional truncated covariance, drift, path factors and signed fourth-order kernel, not only a terminal comparison estimate.',
 'ben:maximum':'Candidate reuse after checking central symmetry, q>1, v=0 and every truncation/threshold endpoint.',
 'opt:moderate-tail':'The strict scalar tail and lattice-uniform all-threshold qualifications must match the actual archived proof dependency closure.',
 'lower:shift-comparison':'Candidate reuse of the Taylor/CDF comparison after checking independence, signs and finite second moments.',
 'lower:family-properties':'The new covariance/rank/correlation-gap and Gaussian-width calibration require explicit bridges to the actual common symmetric construction.'}

C2=[
 ('C2.1',[6384,6402],'Signed indices, maxima and the two pseudometrics',
  ['Finite index type has a zero point and two distinct signed slots for each of p>=1 coordinates; its cardinality is 2*p+1.',
   'Evaluate X_t=t dot W and Y_t=t dot Z; prove zero and both pointwise maximum identities.',
   'Define d1=delta*1_{s!=t} on original indices, and d2 from the Gaussian second moment; prove finite nonnegative symmetric triangle properties.'],
  ['No quotienting of signed-coordinate labels is permitted for d1.'], []),
 ('C2.2',[6404,6417],'Bernstein mixed tails for actual bounded-sum contrasts',
  ['Derive measurability, integrability, centering and independence of every contrast from the bounded-sum assumptions.',
   'Prove the almost-sure contrast envelope 2*delta and variance sum equal to the matching Gaussian contrast variance.',
   'Apply scalar Bernstein MGF to each sign and optimize with explicit universal constants; handle s=t and zero contrast variance.'],
  ['The mixed-tail hypothesis is an output, not an admissible extra premise of C.2.',
   'A Bernstein theorem supplied with an assumed MGF or assumed variance identity does not by itself close this passage.'],
  ['Scalar Bernstein MGF implementation and Chernoff optimization in the archive; exact expanded type and new instantiation pending.',
   'RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf_nonneg']),
 ('C2.3',[6419,6435],'Admissible-subset functional and metric scaling',
  ['Match nonempty finite subsets and indexed slots, including the singleton first level.',
   'Identify the weights 2^k and sqrt(2)^k with the printed exponents.',
   'Prove finite metric costs and justify real values before metric homogeneity and tail-scale factors are used.'],
  ['The printed later subsets must be nonempty so that distance to a net is defined; the library makes this convention explicit.'],
  ['GenericChaining.gamma_eq_finset','GenericChaining.gamma_mul_nnreal']),
 ('C2.4',[6437,6448],'Dirksen expectation at zero and the variance-one extra term',
  ['Supply HasMixedTail from C2.2 and integrable increments, then instantiate Dirksen at the zero index.',
   'Use C2.1 to identify the left-hand maximum and C2.3 for both scaled functionals.',
   'For every signed coordinate use Cauchy--Schwarz and unit marginal variance to show E|X_t|<=1; the zero slot contributes zero.'],
  ['Do not assume the desired maximum comparison or a bound on E||W||infinity as an input.'],
  ['GenericChaining.dirksen_expectation']),
 ('C2.5',[6450,6461],'Singleton-then-full discrete nets and logarithmic cost',
  ['Witness the smallest cutoff with 2^(2^k)>=2*p+1 and prove admissibility at level zero.',
   'Sum the finite dyadic approximation errors and bound the cutoff by log(2*p+1).',
   'Prove the final comparison log(2*p+1)<=C*log(e*p), including p=1.'],
  ['p>=1 implies |T|>=3 and the printed cutoff is positive, so T_0 remains a singleton.'],
  ['GenericChaining.gamma1_discrete_le_cutoff','GenericChaining.gamma1_discrete_le_log2']),
 ('C2.6',[6463,6476],'Concrete Gaussian canonical geometry and majorizing measures',
  ['Construct a covariance factor (or prove a supported representation) from positive semidefiniteness of Cov(W), allowing singularity.',
   'Match Gaussian contrast second moments with squared Euclidean distances for the signed coefficient vectors.',
   'Identify the one-sided signed-and-zero Gaussian maximum with ||Z||infinity and apply the actual audited majorizing-measure theorem.',
   'If quotienting is used, prove surjectivity, zero-contrast almost-sure equality and preservation of the functional and maximum.'],
  ['The Gaussian comparison/lower chaining inequality cannot be an assumed premise of the paper theorem.',
   'Exact positive and negative correlations may identify canonical points but must not identify the original discrete indices.'],
  ['GenericChaining.gamma2_le_gaussianWidth','GenericChaining.gamma_pullback','GenericChaining.maximum_ae_eq_of_zero_contrasts','RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent']),
 ('C2.7',[6478,6484],'Assemble and absorb the constant uniformly in positive dimension',
  ['Combine both chaining bounds with the extra term <=2.',
   'Prove g_Sigma>=E|Z_1|=sqrt(2/pi)>0 from a unit Gaussian marginal.',
   'Choose the final universal constant before n,p,delta,the summands and covariance; include p=1 explicitly.'],
  ['No asymptotic dimension assumption, nonsingularity assumption or small-envelope assumption is present in Lemma C.2.'], [])]

def generate():
    inv,raw,cov,old,old_data=inputs(); oe=envs(old_data); ne={k:envs(v) for k,v in raw.items()}
    old_by={e['label']:e for e in old['entries'] if e.get('in_scope')}
    meta={'schema_version':1,'paper':inv['paper'],'snapshot':inv['snapshot'],
          'inventory_sha256':digest(INVENTORY.read_bytes()),'source_files':inv['source_files'],
          'status_policy':'Open means no compiled new statement/passage correspondence is claimed. Historical receipts remain historical; candidates are not accepted mappings.'}
    rows=[]
    for s in inv['statements']:
        label=s['tex_label']; excluded=s['statement']=='Conjecture 1'; candidate=old_by.get(label)
        same=bool(candidate and ne[s['source']][label]==oe[label])
        reuse=('excluded' if excluded else 'new_named_result' if not candidate else
               'verbatim_statement_candidate' if same else
               'new_width_calibration_using_historical_components' if label in ['opt:symmetric-lower','opt:q4-lower','opt:q4-growing','lower:dense','lower:sparse','lower:family-properties'] else
               'wrapper_or_strengthening_candidate')
        rows.append({'id':sid(label),'statement':s['statement'],'tex_label':label,'title':s['title'],
          'location':location(inv,raw,s['source'],s['lines']),
          'statement_environment_sha256':digest(ne[s['source']][label]),
          'status':'excluded' if excluded else 'open','printed_proof_status':'excluded' if excluded else 'open',
          'reuse_classification':reuse,'source_environment_bytes_identical':same,
          'review_obligation':'Excluded conjecture; no proof or certification is requested.' if excluded else REUSE_NOTES.get(label,'New statement: no archived named-label counterpart. Build the mathematical proof and correspondence from the frozen source.'),
          'archive_candidate':None if not candidate else {'label':label,'declaration':candidate.get('lean_declaration'),
            'statement_environment_sha256':digest(oe[label]),'expanded_type':candidate.get('expanded_lean_type'),
            'expanded_type_provenance':'saved archive statement map, not a fresh execution in this release',
            'source_reference':s.get('archived_source_url'),'accepted_in_new_release':False},
          'lean_declarations':[],'expanded_types':[],'dependency_declarations':[],'proof_passage_ids':
            [p[0] for p in C2] if label=='intrinsic:lem:maximum' else
            [f'C1.G.{i}' for i in range(1,9)] if label=='lem:concentration' and (HERE/'c1-gaussian-passages.json').exists() else [],'build_receipt':None,'audit_receipt':None})
    assert sum(r['archive_candidate'] is not None for r in rows)==29
    assert [r['statement'] for r in rows if r['source_environment_bytes_identical']]==['Lemma B.3']
    passage=[]
    for ident,lines,title,premises,limits,deps in C2:
        passage.append({'id':ident,'statement_id':sid('intrinsic:lem:maximum'),'title':title,
          'location':location(inv,raw,'main',lines),'status':'open','inference_obligations':premises,
          'scope_constraints':limits,'audited_dependency_candidates':deps,
          'generic_chaining_pin':'b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc' if any(x.startswith('GenericChaining.') for x in deps) else None,
          'new_declarations':[],'expanded_types':[],'dependency_bindings':[],'reading_order_review':None,
          'build_receipt':None,'transitive_axiom_receipt':None})
    envrows=[]
    for i,p in enumerate(inv['explicit_proof_environments'],1):
        matched=[sid(l) for l in re.findall(r'\\ref\{([^}]+)\}',p.get('caption') or '') if any(s['tex_label']==l for s in inv['statements'])]
        if p['source']=='main' and p['lines']==[6384,6484]: matched=[sid('intrinsic:lem:maximum')]
        envrows.append({'id':f"P-{p['source']}-{i:02d}",'location':location(inv,raw,p['source'],p['lines']),
          'caption':p.get('caption'),'statement_ids':matched,'status':'open',
          'subdivision_status':'C2.1--C2.7 recorded separately' if p['lines']==[6384,6484] else 'awaiting substantive subdivision',
          'passage_ids':[p[0] for p in C2] if p['lines']==[6384,6484] else []})
    arows=[]
    for p in cov['proof_steps']:
        arows.append({'archive_id':p['id'],'archive_fragment':p.get('fragment'),'archive_classification':p['classification'],
          'archive_location':{'path':cov['frozen_manuscript']['path'],'commit':cov['frozen_manuscript']['commit'],
             'lines':p['source_lines'],'sha256':digest(span(old_data,p['source_lines']))},
          'archive_declarations':p.get('new_declarations',[]),'archive_labels':p.get('labels',[]),
          'new_release_status':'historical_candidate_only','new_passage_ids':[],
          'note':'Historical accepted passage is not a proof of a new frozen passage.'})
    summary={'named_results_in_scope':40,'excluded_conjectures':1,'statement_rows':len(rows),
      'historical_proved_label_matches':29,'identical_statement_environments':1,
      'new_named_results_without_historical_label':11,'explicit_proof_environments':len(envrows),
      'archived_accepted_same_argument_passages':sum(p['archive_classification']=='SAME_ARGUMENT' for p in arows),
      'archived_scope_repair_records':sum(p['archive_classification']!='SAME_ARGUMENT' for p in arows),
      'new_accepted_statement_correspondences':0,'new_accepted_passage_correspondences':0}
    archives={'statement_map_path':str(OLD_STATEMENTS.relative_to(ROOT)),'statement_map_sha256':digest(OLD_STATEMENTS.read_bytes()),
      'coverage_path':str(COVERAGE.relative_to(ROOT)),'coverage_sha256':digest(COVERAGE.read_bytes()),
      'frozen_manuscript':cov['frozen_manuscript'],
      'positive_derivative_qualification':'Archive derivative-envelope results apply to integer q>=1. Literal q=0 claims were refuted. Current source explicitly says positive integer at main lines3138 and3170; no order-zero conclusion is mapped.',
      'fresh_replay_status':'not performed by this ledger generator','fresh_lean_execution_status':'not performed by this ledger generator'}
    return {'statements.json':meta|{'summary':summary,'archive_inputs':archives,'statements':rows},
      'c2-passages.json':meta|{'statement_location':location(inv,raw,'main',[6376,6382]),
        'setup_locations':[location(inv,raw,'main',lines) for lines in [[145,157],[169,176],[220,228]]],
        'passages':passage},
      'proof-environments.json':meta|{'coverage_note':inv['coverage_note'],'proof_environments':envrows},
      'archive-candidates.json':meta|{'archive_inputs':archives,'passages':arows}}

def check():
    inv,raw,cov,old,old_data=inputs(); count=0
    for filename,key in [('statements.json','statements'),('c2-passages.json','passages'),('proof-environments.json','proof_environments')]:
        data=read_json(HERE/filename)
        if data['snapshot']!=inv['snapshot'] or data['inventory_sha256']!=digest(INVENTORY.read_bytes()): raise ValueError('snapshot/inventory changed')
        for row in data[key]:
            loc=row['location']; got=location(inv,raw,loc['source'],loc['lines'])
            if loc!=got: raise ValueError(f'span changed: {filename}:{row.get("id")}')
            count+=1
    c1path=HERE/'c1-gaussian-passages.json'
    if c1path.exists():
        c1=read_json(c1path)
        for loc in [c1['statement_location'], *(r['location'] for r in c1['passages'])]:
            if loc != location(inv,raw,loc['source'],loc['lines']): raise ValueError('C1 Gaussian span changed')
            count+=1
    c2=read_json(HERE/'c2-passages.json')
    for loc in [c2['statement_location'], *c2['setup_locations']]:
        if loc != location(inv,raw,loc['source'],loc['lines']): raise ValueError('setup/statement span changed')
        count+=1
    data=read_json(HERE/'archive-candidates.json')
    archive_inputs=data['archive_inputs']
    if archive_inputs['statement_map_sha256'] != digest(OLD_STATEMENTS.read_bytes()): raise ValueError('archived statement map changed')
    if archive_inputs['coverage_sha256'] != digest(COVERAGE.read_bytes()): raise ValueError('archived coverage changed')
    for row in data['passages']:
        loc=row['archive_location']
        if digest(span(old_data,loc['lines']))!=loc['sha256']: raise ValueError(f'archive span changed: {row["archive_id"]}')
    statements=read_json(HERE/'statements.json')['statements']
    excluded=[r for r in statements if r['status']=='excluded']
    if len(excluded)!=1 or excluded[0]['tex_label']!='conj:sharp-unrestricted': raise ValueError('conjecture exclusion changed')
    print(json.dumps({'status':'PASS_SOURCE_IDENTITY_ONLY','snapshot':inv['snapshot'],
      'checked_new_source_spans':count,'checked_archive_spans':len(data['passages']),
      'mathematical_correspondence_certified':False},indent=2))

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-initial',action='store_true');parser.add_argument('--check',action='store_true');a=parser.parse_args()
    if a.write_initial:
        outputs=generate()
        for name in outputs:
            if (HERE/name).exists(): raise SystemExit(f'refusing to overwrite {name}; update mappings deliberately')
        for name,data in outputs.items(): (HERE/name).write_text(json.dumps(data,indent=2)+'\n')
    if a.check or not a.write_initial:check()
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Strict passage/type audit in the frozen, clean Supplement G checkout."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
CLEAN = Path('/workspace/rectangle-clt-supplement-g-clean/lean-rectangle-clt-arxiv-v1')
OUTPUT = PROJECT / 'evidence/supplement-g-clean-mapping-complete'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    runfile = PROJECT / 'evidence/supplement-g-clean-checkpoint/run.json'
    run = json.loads(runfile.read_text())
    assert run['status'] == 'passed' and not run['initial_git_status']
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=CLEAN, text=True).strip()
    for f, expected in run['source_identity']['files'].items():
        assert sha(CLEAN / f) == sha(PROJECT / f) == expected, f
    OUTPUT.mkdir(exist_ok=False)
    ledgers = sorted((PROJECT / 'correspondence').glob('supplemental-g-*-passages.json'))
    targets = set()

    def names(v):
        if isinstance(v, str):
            if re.fullmatch(r'RectangleCLTArxivV1\.[A-Za-z0-9_]+', v):
                targets.add(v)
            elif re.fullmatch(r'cap[A-Za-z0-9_]+', v):
                targets.add('RectangleCLTArxivV1.' + v)
        elif isinstance(v, list):
            for w in v:
                names(w)
        elif isinstance(v, dict):
            for k, w in v.items():
                if k in ('theorems', 'mapped_declarations', 'final_theorems',
                         'public_declarations', 'public_endpoints', 'strict_checked_declarations',
                         'endpoints', 'declaration', 'name', 'endpoint'):
                    names(w)
                elif isinstance(w, (list, dict)):
                    names(w)

    for f in ledgers:
        d = json.loads(f.read_text())
        if 'declarations' in d:
            targets.update(d['declarations'])
            names(d['passages'])
        else:
            names(d)
    targets.update('RectangleCLTArxivV1.' + n for n in (
        'cap_seededFourthRemainder_rank_complementary_bound',
        'cap_seededFourthRemainder_rank_intervalIntegrable',
        'cap_seededFourthRemainder_rank_abs_intervalIntegrable',
        'proposition_G1_dimension_log_cap_normalized'))
    template = (PROJECT / 'evidence/main-results-clean-mapping/TypesAndAudit.lean').read_text()
    template = template.replace('import RectangleCLTArxivV1.CapClosedIntervals\n', '').replace(
        'import RectangleCLTArxivV1.LowerLemmaF1Support\n', '')
    lo = template.index('  let targets := #[')
    hi = template.index('  let mut queue :=', lo)
    template = template[:lo] + '  let targets := #[\n' + ',\n'.join(
        '    ``' + n for n in sorted(targets)) + ']\n' + template[hi:]
    template = template.replace('Additional main statements, qualified E1, G2/H2 and mapped source steps',
                                'Exact normalized G1, actual rank G3 and their mapped proof steps')
    harness = OUTPUT / 'TypesAndAudit.lean'
    harness.write_text(template)
    (OUTPUT / 'requested-targets.json').write_text(json.dumps(sorted(targets), indent=2) + '\n')
    receipt = dict(scope='Clean Supplement G passage/type/transitive-axiom audit',
                   release_wide_certification=False, source_commit=run['source_commit'],
                   initial_git_status='', base_clean_checkpoint=dict(
                       path=str(runfile.relative_to(PROJECT)), sha256=sha(runfile)),
                   source_identity_unchanged=True, targets=len(targets),
                   ledger_sha256={str(p.relative_to(PROJECT)): sha(p) for p in ledgers},
                   harness=str(harness.relative_to(PROJECT)), harness_sha256=sha(harness),
                   allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
                   started_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   status='running')
    receiptfile = OUTPUT / 'receipt.json'
    receiptfile.write_text(json.dumps(receipt, indent=2) + '\n')
    log = OUTPUT / 'types-and-audit.json'
    with log.open('wb') as stream:
        code = subprocess.run(['lake', 'env', 'lean', str(harness)], cwd=CLEAN,
                              env=os.environ.copy(), stdout=stream, stderr=subprocess.STDOUT).returncode
    receipt.update(exit_code=code, status='passed' if code == 0 else 'failed',
                   finished_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   log=str(log.relative_to(PROJECT)), log_sha256=sha(log))
    receiptfile.write_text(json.dumps(receipt, indent=2) + '\n')
    if code:
        raise SystemExit('Mapped type/axiom audit failed; preserved receipt and log')
    data = json.loads(log.read_text())
    assert len(data['endpoints']) == len(targets)
    blocked = {'RectangleCLT.Companion.SplitV4.relativeFourthMomentCLT',
               'RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists'}
    assert not blocked.intersection(r['name'] for r in data['project_dependency_graph'])
    print(f'PASS: {len(targets)} mapped declarations; {len(data["project_dependency_graph"])} project nodes')


if __name__ == '__main__':
    main()

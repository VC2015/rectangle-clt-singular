#!/usr/bin/env python3
"""Freeze and strictly audit the native Appendix H pair-reference leaf."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PROJECT = Path(__file__).resolve().parents[2]
OUTPUT = PROJECT / 'evidence/supplement-h-projected-reference/independent-root-checkpoint-1'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def main():
    OUTPUT.mkdir(parents=True, exist_ok=False)
    modules = ['SupplementalHPairProjectionLaw', 'SupplementalHPairReferenceTransport', 'SupplementalHPhysicalConcentration']
    sources = [PROJECT / ('RectangleCLTArxivV1/' + module + '.lean') for module in modules]
    targets = ['RectangleCLTArxivV1.' + n for source in sources for n in re.findall(
        r'^(?:theorem|def) ([A-Za-z0-9_]+)', source.read_text(), re.M)]
    files = {}

    def visit(module):
        path = PROJECT / (module.replace('.', '/') + '.lean')
        if not path.exists() or str(path.relative_to(PROJECT)) in files:
            return
        files[str(path.relative_to(PROJECT))] = sha(path)
        for dependency in re.findall(r'^import (RectangleCLTArxivV1\.[A-Za-z0-9_]+)',
                                     path.read_text(), re.M):
            visit(dependency)

    for module in modules:
        visit('RectangleCLTArxivV1.' + module)
    template = (PROJECT / 'evidence/main-results-clean-mapping/TypesAndAudit.lean').read_text()
    template = re.sub(r'^import RectangleCLTArxivV1[^\n]*\n', '', template, flags=re.M)
    template = ''.join('import RectangleCLTArxivV1.' + module + '\n' for module in modules) + template
    lo, hi = template.index('  let targets := #['), template.index('  let mut queue :=')
    template = template[:lo] + '  let targets := #[\n' + ',\n'.join(
        '    ``' + n for n in targets) + ']\n' + template[hi:]
    template = template.replace('Additional main statements, qualified E1, G2/H2 and mapped source steps',
                                'Independent actual projected Gaussian pair-reference transport and physical layer concentration')
    harness = OUTPUT / 'TypesAndAudit.lean'
    harness.write_text(template)
    (OUTPUT / 'targets.json').write_text(json.dumps(targets, indent=2) + '\n')
    receiptfile = OUTPUT / 'run.json'
    receipt = dict(scope='Actual original-coordinate pair-reference transport and physical concentration only; H matrix estimates remain separate',
                   release_wide_certification=False, initial_checkout_clean=False,
                   source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
                   source_identity=files, strict_targets=len(targets),
                   allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
                   started_at_utc=now(), commands=[], status='running')

    def save():
        receiptfile.write_text(json.dumps(receipt, indent=2) + '\n')

    def run(label, argv):
        log = OUTPUT / (label + '.log')
        row = dict(label=label, argv=argv, started_at_utc=now(), log=str(log.relative_to(PROJECT)))
        receipt['commands'].append(row)
        save()
        with log.open('wb') as stream:
            code = subprocess.run(argv, cwd=PROJECT, env=os.environ.copy(),
                                  stdout=stream, stderr=subprocess.STDOUT).returncode
        row.update(exit_code=code, finished_at_utc=now(), log_sha256=sha(log))
        save()
        if code:
            raise RuntimeError(f'{label} failed; original log preserved')
        return log

    try:
        save()
        run('build', ['lake', 'build'] + ['RectangleCLTArxivV1.' + module for module in modules])
        for source in sources:
            run('force-' + source.stem, ['lake', 'env', 'lean', str(source.relative_to(PROJECT))])
        log = run('types-and-strict-audit', ['lake', 'env', 'lean', str(harness)])
        data = json.loads(log.read_text())
        assert len(data['endpoints']) == len(targets)
        for f, expected in files.items():
            assert sha(PROJECT / f) == expected, f
        (OUTPUT / 'expanded-types.json').write_text(json.dumps(data, indent=2) + '\n')
        receipt.update(status='passed', full_type_count=len(data['endpoints']),
                       project_dependency_nodes=len(data['project_dependency_graph']),
                       expanded_types_sha256=sha(OUTPUT / 'expanded-types.json'), finished_at_utc=now())
        save()
    except Exception as error:
        receipt.update(status='failed', error=str(error), finished_at_utc=now())
        save()
        raise
    print(f'PASS: {len(targets)} projected-reference/physical-concentration declarations, all source hashes unchanged')


if __name__ == '__main__':
    main()

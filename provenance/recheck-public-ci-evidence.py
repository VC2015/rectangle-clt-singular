#!/usr/bin/env python3
"""Recheck the preserved CI evidence against the selected public Git tree.

The original comparator is kept unchanged. Its one whole-repository tree
comparison is adapted to the filtered tree; all source, log, dependency,
declaration, archive and preserved API-metadata checks remain in force.
This validates archived evidence and does not execute Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension'
CI = EVIDENCE / 'logs-ci-42420549190'
ORIGINAL = CI / 'compare_evidence.py'
ORIGINAL_SHA = '3c3b1a2f244ddd4709197ae819368dc2baab702315997d086f2c429d6c1f8677'
PUBLIC_TREE = 'c6299a33653aff7107858007b3df7272cb2422a0'
source = ORIGINAL.read_text()
assert hashlib.sha256(ORIGINAL.read_bytes()).hexdigest() == ORIGINAL_SHA
old = 'require(subprocess.check_output(["git", "rev-parse", R + "^{tree}"], cwd=args.repo).decode().strip() == TREE, "Immutable R Git tree differs")'
new = old.replace('== TREE,', '== "' + PUBLIC_TREE + '",').replace('Immutable R Git tree differs', 'Filtered public R Git tree differs')
assert source.count(old) == 1
adapted = source.replace(old, new)
namespace = {'__file__': str(ORIGINAL), '__name__': 'public_archive_ci_comparator'}
exec(compile(adapted, str(ORIGINAL), 'exec'), namespace)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
if args.output.exists():
    raise SystemExit('Choose a new output path; existing receipts are not overwritten.')
report = namespace['compare'](SimpleNamespace(
    ci=CI/'extracted/split-v4-checkpoint', baseline=CI/'extracted/split-v4-baseline',
    local=EVIDENCE/'logs-checkpoint-92896b8', merge_metadata=CI/'api-ci-merge-commit.json',
    run_metadata=CI/'api-run-complete.json', job_metadata=CI/'api-jobs-complete.json',
    check_metadata=CI/'api-check-runs-complete.json', artifact_metadata=CI/'api-artifact.json',
    archive=CI/'split-v4-lean-command-evidence-42420549190.zip', extracted_root=CI/'extracted',
    extraction_manifest=CI/'extraction-manifest.json',
    local_validation=EVIDENCE/'CHECKPOINT_VALIDATION.json', repo=ROOT))
report['public_export_adaptation'] = {
    'original_comparator_sha256': ORIGINAL_SHA,
    'adapted_comparator_sha256': hashlib.sha256(adapted.encode()).hexdigest(),
    'wrapper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'original_full_tree': namespace['TREE'], 'filtered_public_tree': PUBLIC_TREE,
    'changed_check': 'Compare the local proof tree to its filtered public tree; retain original whole-tree identities in the preserved CI API metadata checks.',
    'unchanged_checks': 'Every recorded Lean source, configuration, manuscript, log, dependency, declaration binding, artifact and original API-metadata check.',
    'new_lean_execution': False}
args.output.write_text(json.dumps(report, indent=2) + '\n')
print('Preserved independent CI evidence passed against the filtered public archive.')
print(args.output)

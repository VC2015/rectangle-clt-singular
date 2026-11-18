#!/usr/bin/env python3
"""Copy completed, source-identical fresh archival artifacts into current caches.

This writes only ignored .lake/build files and this directory's transfer receipt.
It never edits a Lean source, manifest, manuscript, or historical receipt.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path('/workspace/rectangle-clt-frozen-proof')
DESTINATION = Path('/workspace/rectangle-clt-singular')
RECEIPT = HERE / 'cache-transfer.json'
PACKAGES = ('lean-kane', 'lean-rectangle-clt-local', 'lean-rectangle-clt-singular')


def sha256(data):
    return hashlib.sha256(data).hexdigest()


record = json.loads(RECEIPT.read_text()) if RECEIPT.exists() else {
    'source_worktree': str(SOURCE),
    'destination_worktree': str(DESTINATION),
    'original_proof_commit': '92896b8a2a4099357486587d17ca1921a3dba161',
    'public_proof_commit': '7f515de98933646a494cca2438dac23ebf0fc2fa',
    'method': 'Copy completed build artifacts only after comparing exact Lean source bytes; no mutable build directory symlinks.',
    'new_lean_execution': True,
    'historical_sources_or_receipts_modified': False,
    'artifacts': {},
}
copied = 0
modules = 0
for package in PACKAGES:
    build = SOURCE / package / '.lake/build'
    for trace in sorted((build / 'lib/lean').rglob('*.trace')):
        module = trace.relative_to(build / 'lib/lean').with_suffix('')
        source_lean = SOURCE / package / module.with_suffix('.lean')
        destination_lean = DESTINATION / package / module.with_suffix('.lean')
        if not source_lean.is_file() or not destination_lean.is_file():
            continue
        source_bytes = source_lean.read_bytes()
        if source_bytes != destination_lean.read_bytes():
            raise SystemExit('Refusing different source bytes: ' + str(destination_lean))
        olean = build / 'lib/lean' / module.with_suffix('.olean')
        if not olean.is_file() or not Path(str(olean) + '.hash').is_file():
            continue
        modules += 1
        candidates = [build / 'lib/lean' / Path(str(module) + suffix)
                      for suffix in ('.olean', '.olean.hash', '.ilean', '.ilean.hash', '.trace')]
        candidates += [build / 'ir' / Path(str(module) + suffix) for suffix in ('.c', '.c.hash')]
        for source in candidates:
            if not source.is_file():
                continue
            relative = source.relative_to(SOURCE)
            destination = DESTINATION / relative
            data = source.read_bytes()
            digest = sha256(data)
            destination.parent.mkdir(parents=True, exist_ok=True)
            if not destination.exists() or sha256(destination.read_bytes()) != digest:
                temporary = destination.with_name(destination.name + '.archive-transfer.tmp')
                temporary.write_bytes(data)
                os.replace(temporary, destination)
                copied += 1
            record['artifacts'][str(relative)] = {
                'source': str(source), 'destination': str(destination),
                'artifact_sha256': digest, 'lean_source_path': str(source_lean.relative_to(SOURCE)),
                'lean_source_sha256': sha256(source_bytes),
            }

record['observed_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['completed_source_identical_module_count'] = modules
record['artifact_count'] = len(record['artifacts'])
RECEIPT.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
print(json.dumps({'source_identical_modules': modules, 'artifacts_copied_this_run': copied,
                  'recorded_artifacts': record['artifact_count']}))

#!/usr/bin/env python3
"""Validate a completed frozen checkpoint and pack its unchanged raw evidence."""
import datetime
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile
import time

HERE = Path(__file__).resolve().parent
RAW = HERE / 'fresh-lean-checkpoint'
FROZEN = Path('/workspace/rectangle-clt-frozen-proof/lean-rectangle-clt-singular')
PROOF = '92896b8a2a4099357486587d17ca1921a3dba161'


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


while True:
    run = json.loads((RAW / 'run.json').read_text())
    if 'finished_at' in run:
        break
    try:
        os.kill(72962, 0)
    except ProcessLookupError:
        raise SystemExit('Original runner exited without a completed run.json; no validation or bundle claimed.')
    time.sleep(5)

receipt = HERE / '12-fresh-checkpoint-validator.command.json'
log = HERE / '12-fresh-checkpoint-validator.log'
assert not receipt.exists() and not log.exists(), 'Refusing to overwrite evidence.'
argv = ['python3', 'split-v4-certification/printed-proof-extension/verify_record.py',
        '--logs', str(RAW), '--proof-commit', PROOF, '--validate-only']
record = {'argv': argv, 'cwd': str(FROZEN), 'started_at': now(),
          'new_lean_execution': False, 'validates_new_lean_execution': True,
          'interpretation': 'Validation of the new frozen 7 November checkpoint, not certification of the 16 November manuscript.',
          'status': 'running'}
receipt.write_text(json.dumps(record, indent=2) + '\n')
with log.open('wb') as stream:
    process = subprocess.run(argv, cwd=FROZEN, stdout=stream, stderr=subprocess.STDOUT)
record.update(status='completed', finished_at=now(), exit_code=process.returncode,
              log_sha256=digest(log), checkpoint_run_sha256=digest(RAW / 'run.json'))
receipt.write_text(json.dumps(record, indent=2) + '\n')
if process.returncode:
    raise SystemExit('Frozen validator failed; see the recorded receipt and log. No success bundle claimed.')

paths = sorted(RAW.iterdir())
expected = {'run.json', *(entry['log'] for entry in run['commands'])}
assert {path.name for path in paths} == expected
assert all(path.is_file() and not path.is_symlink() for path in paths)
for command in run['commands']:
    assert digest(RAW / command['log']) == command['log_sha256']

bundle = HERE / 'fresh-lean-checkpoint.tar.gz'
manifest = HERE / 'fresh-lean-checkpoint.bundle.json'
assert not bundle.exists() and not manifest.exists(), 'Refusing to overwrite evidence.'
members = {f'fresh-lean-checkpoint/{path.name}': digest(path) for path in paths}
with bundle.open('wb') as output:
    with gzip.GzipFile(filename='', fileobj=output, mode='wb', mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            for path in paths:
                info = archive.gettarinfo(str(path), f'fresh-lean-checkpoint/{path.name}')
                info.uid = info.gid = 0
                info.uname = info.gname = ''
                info.mtime = 0
                with path.open('rb') as source:
                    archive.addfile(info, source)
with tarfile.open(bundle, 'r:gz') as archive:
    assert {item.name for item in archive.getmembers()} == set(members)
    for item in archive.getmembers():
        stream = archive.extractfile(item)
        assert stream is not None
        assert hashlib.sha256(stream.read()).hexdigest() == members[item.name]
manifest.write_text(json.dumps({'created_at': now(), 'bundle': bundle.name,
    'bundle_sha256': digest(bundle), 'bundle_bytes': bundle.stat().st_size,
    'uncompressed_bytes': sum(path.stat().st_size for path in paths),
    'method': 'Deterministic gzip/tar of the completed raw evidence; original logs remain unchanged and each member was read back and hash-checked.',
    'member_sha256': members, 'validator_receipt': receipt.name,
    'commands': len(run['commands']), 'required_commands_passed': run['required_commands_passed'],
    'paper_certified': False}, indent=2) + '\n')
print(json.dumps({'validator_exit_code': process.returncode, 'commands': len(run['commands']),
                  'bundle_bytes': bundle.stat().st_size, 'bundle_manifest': str(manifest)}), flush=True)

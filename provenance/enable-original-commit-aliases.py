#!/usr/bin/env python3
"""Resolve archived commit identifiers to their public, filtered counterparts.

This creates local Git replacement refs. It does not fetch private objects,
change tracked files, or recreate the original full-repository commits.
The mapping and the retained dates remain available for independent review.
"""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
def git(*args, check=True):
    return subprocess.run(['git', *args], cwd=ROOT, text=True,
                          capture_output=True, check=check)

count = 0
for line in (ROOT / 'provenance/commit-map.txt').read_text().splitlines()[1:]:
    original, public = line.split()
    if set(public) == {'0'} or original == public:
        continue
    assert len(original) == len(public) == 40
    git('--no-replace-objects', 'cat-file', '-e', public + '^{commit}')
    ref = 'refs/replace/' + original
    existing = git('show-ref', '--hash', '--verify', ref, check=False)
    if existing.returncode == 0:
        if existing.stdout.strip() != public:
            raise SystemExit('Refusing to replace a conflicting local alias: ' + ref)
    else:
        git('update-ref', ref, public, '0' * 40)
    count += 1
print(f'Enabled {count} local original-to-public commit aliases.')
print('These aliases expose only the filtered public trees, not the private original trees.')

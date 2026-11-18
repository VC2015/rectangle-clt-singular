#!/usr/bin/env python3
"""Read-only import-closure/cache preflight for frozen archival module targets."""
import datetime
import functools
import json
from pathlib import Path
import re
import sys

FROZEN = Path('/workspace/rectangle-clt-frozen-proof')
CURRENT = Path('/workspace/rectangle-clt-singular')
MATHLIB = Path('/workspace/generic-chaining/.lake/packages/mathlib')
PROJECT = {}
for package in ('lean-kane', 'lean-rectangle-clt-local', 'lean-rectangle-clt-singular'):
    for source in (FROZEN / package).rglob('*.lean'):
        if '.lake' not in source.parts:
            PROJECT[str(source.relative_to(FROZEN / package).with_suffix('')).replace('/', '.')] = source


@functools.lru_cache(None)
def imports(source):
    text = source.read_text()
    clean = []
    index = depth = 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == '/-':
            depth += 1
            index += 2
        elif depth and pair == '-/':
            depth -= 1
            index += 2
        elif depth:
            index += 1
        elif pair == '--':
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
        else:
            clean.append(text[index])
            index += 1
    return [module for line in ''.join(clean).splitlines()
            if re.match(r'^\s*import\s+', line) for module in line.strip()[7:].split()]


results = []
for target in sys.argv[1:]:
    pending = [target]
    reached = set()
    missing_mathlib = []
    missing_current_project = []
    missing_frozen_project = []
    for_source = target in PROJECT
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        if module == 'Mathlib' or module.startswith('Mathlib.'):
            source = MATHLIB / (module.replace('.', '/') + '.lean')
            artifact = MATHLIB / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
            if not artifact.exists():
                missing_mathlib.append(module)
        elif module in PROJECT:
            source = PROJECT[module]
            relative = source.relative_to(FROZEN)
            package = relative.parts[0]
            artifact = Path(package) / '.lake/build/lib/lean' / Path(*relative.parts[1:]).with_suffix('.olean')
            if not (CURRENT / artifact).exists():
                missing_current_project.append(module)
            if not (FROZEN / artifact).exists():
                missing_frozen_project.append(module)
        else:
            continue
        if source.exists():
            pending.extend(imports(source))
    results.append({'target': target, 'target_source_found': for_source,
                    'missing_mathlib': sorted(missing_mathlib),
                    'missing_current_project': sorted(missing_current_project),
                    'missing_frozen_project': sorted(missing_frozen_project)})
print(json.dumps({'observed_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'method': 'Read frozen imports after stripping nested block and line comments; inspect existing oleans without invoking Lean.',
                  'targets': results}, indent=2))

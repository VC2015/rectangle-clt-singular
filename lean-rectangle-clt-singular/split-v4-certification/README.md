# Split-V4 complete Lean certificate

Reader-facing report: [REPORT.md](REPORT.md) · [PDF](REPORT.pdf).

The frozen proof source is `69f89747f4b845491b75cb23134c056bfbcd40f7`.
All 31 proved named statements and the required analytic chains are checked;
Conjecture 1 is excluded. The final isolated run passed all 167 required
commands, recorded 3,751 kernel dependency declarations, and audited 5,757
imported companion theorem declarations. Only `propext`, `Classical.choice`
and `Quot.sound` occur transitively. The independent CI run for the same
proof source passed its eight-command pristine baseline and all 167
checkpoint commands.

The checked scope is Theorems 1–8, Corollaries 1–3, Propositions 1–3,
Lemmas 1–2, A.1, B.1–B.5, C.1, E.1, F.1–F.3 and G.1–G.4.
The [verification record](../SPLIT_V4_VERIFICATION.json),
[statement map](statement-map.json), [dependency map](dependency-map.json),
[completed obligations](OPEN_OBLIGATIONS.md) and
[correspondence review](CORRESPONDENCE_REVIEW.md) give exact endpoint types,
proof-route distinctions and raw execution evidence. Counts overlap and
follow Lean module attribution; they must not be added.

The target is the split-V4 manuscript at handoff commit
`2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`, with SHA-256
`f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`.
The handoff, original inventory, manuscript, analytic audit, and October
verification records remain separate sources of evidence. An analytic review
does not prove a Lean theorem.

Run from `lean-rectangle-clt-singular/`, with Lean's `lake` on `PATH`:

```sh
python3 split-v4-certification/run.py baseline
python3 split-v4-certification/run.py checkpoint
```

`baseline` executes the handoff's version, optional cache, package build, and
five audit commands in that order. `checkpoint` builds the package, directly executes the complete imported
companion audit, and builds every
new module under `RectangleCLTCompanion/SplitV4/`, then directly executes each
new `*Audit.lean` file. Direct execution regenerates theorem-type and axiom
output even when Lake can reuse the compiled module.

Use `--plan` to inspect commands without running them. `--skip-cache` omits
the optional cache download. `--stream` displays command output as it arrives
and retains the same exact bytes in the command log. CI enables streaming so
long builds show their progress. `--output PATH` selects a new or empty directory;
the runner refuses to overwrite previous evidence. No invocation runs
`lake update` or changes the toolchain. The checked-in manifest must keep
mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` and the toolchain at
Lean 4.19.0.

Each output directory contains complete command logs and `run.json`, including
command arguments, working directory, UTC timestamps, durations, exit codes,
log hashes, Git commit and dirty state, Lean source hashes, manifest hashes,
actual dependency revisions, manuscript identity, and frozen-record hashes.
The runner also records `ELAN_HOME`, `MATHLIB_CACHE_DIR`, `XDG_CACHE_HOME`, and
the effective mathlib cache directory, so a read-only default cache or a
deliberate override can be distinguished from a proof failure. Other process
environment variables are omitted.
The record is saved after each command. A toolchain or proof-build failure
stops subsequent commands. A cache failure is recorded separately and allows
the proof build to proceed. Audit failures are recorded while remaining
audits continue for diagnosis. Any changed proof input, dependency revision
mismatch, or failed required command makes the runner exit unsuccessfully.

When the root package has no SplitV4 imports, a baseline's proof-input
fingerprint excludes the new, unimported SplitV4 modules. Their full hashes
are still recorded. This permits independent development while the original
package is being rebuilt. A checkpoint includes all new modules; after root
imports are added, a baseline does too. Avoid modifying inputs during a
checkpoint run.

`required_commands_passed=true` means only that the recorded commands passed
on the recorded input state. Every runner record keeps
`paper_certified=false`: certification of each manuscript statement also
requires exact contract correspondence, a permitted transitive axiom closure,
and separate evidence for the revised proof routes. The statement map and complete certificate require actual current endpoint
contracts and explicit proof-route correspondence in addition to successful
execution.

CI uses `.github/workflows/rectangle-clt-split-v4.yml` and uploads the command
evidence even on failure. Its success covers the checked sources and audits;
the separate mapped certificate establishes the complete manuscript scope.
CI reproduces the historical baseline in a detached worktree at the exact
handoff commit. It copies the current evidence runner into that worktree and
shares the three package caches with the branch checkout. The checkpoint then
builds the current branch sources separately. Cache restoration also accepts
the historical `rectangle-subexp` prefix with the same toolchain and manifest
hashes, retaining the pinned dependencies and prior compiled proofs.
An explicit cache-save step runs even if a later proof or audit fails, so
completed dependency builds remain available for the next run.
The branch and its pull request share a concurrency group, so a newer run
cancels superseded runs for that branch.


## Regenerating the mapped certificate

The recorded baseline is executed from the exact handoff checkout. The CI
workflow creates that detached checkout and copies the evidence runner into
it before running the eight handoff commands. The frozen final checkpoint
uses an independent detached checkout with separate project build directories.
Only pinned third-party package caches are shared locally.

The frozen execution used `--skip-cache`; omit it when a new environment
needs the optional pinned mathlib cache download. Choose a new output directory
for every run. The runner keeps `paper_certified=false` because it records
execution only. The following separate step validates the complete statement
and helper scope before issuing the manuscript certificate:

```sh
python3 split-v4-certification/refresh_record.py \
  --logs split-v4-certification/logs-checkpoint-69f8974 \
  --baseline split-v4-certification/logs-ci-thirty-one-statements/split-v4-baseline/run.json \
  --baseline-workflow-id 42407941681 \
  --ci-provenance split-v4-certification/logs-ci-thirty-one-statements/PROVENANCE.json \
  --certify-complete
```

Add `--validate-only` to perform every check without changing metadata.
The generator verifies each committed Lean/configuration fingerprint, the
preserved handoff inputs, all intended command arguments, log hashes, both
before/after dependency states, actual printed contracts, required helper
presence and constant-first lower endpoints. Independent CI dependency
records are compared exactly with the frozen local records. The CI checkout
commit is recorded separately because a PR build may use a merge or metadata
commit with identical mathematical proof inputs.

Earlier partial maps and receipts remain under `checkpoints/`. The successful
148-command intermediate run at `7b8ef15` is preserved as execution evidence;
it has no separate complete manuscript certificate.

# Split-V4 certification checkpoint

The proof checkpoint is `7bf2325`. Twenty-one current statements have checked
Lean proofs; ten proved statements remain pending. The manuscript is
not certified. The complete imported companion theorem closure passed its
strict axiom audit. The pristine baseline also passed all eight commands in
GitHub CI. Exact command counts, execution outcomes, source hashes and raw
logs are recorded in [the verification record](../SPLIT_V4_VERIFICATION.json).

The checked scope comprises Corollaries 1–2, Theorems 2–3, Propositions 2–3,
Lemmas 1–2, Theorem 4, Lemmas B.3–B.5, Lemma C.1, Lemma E.1, Lemmas F.1–F.3 and G.1–G.4.
The [statement map](statement-map.json), [kernel dependency map](dependency-map.json),
and [open obligations](OPEN_OBLIGATIONS.md) give exact endpoint declarations,
proof-route distinctions, and the remaining mathematical work.

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
five audit commands in that order. `checkpoint` builds the package and every
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
and separate evidence for the revised proof routes. The statement map must
retain pending obligations rather than infer completion from old theorem
names or a successful package build.

CI uses `.github/workflows/rectangle-clt-split-v4.yml` and uploads the command
evidence even on failure. Its success covers the checked sources and audits;
it does not assert that every pending manuscript target has been proved.
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

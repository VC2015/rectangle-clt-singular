# Archival reproduction evidence

This directory concerns the frozen **7 November 2026** proof. Its manuscript
SHA-256 is
`f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`.
It does not certify the 16 November manuscript, its Gaussian-width refinements,
or Supplemental Material G–I. New-paper correspondence is recorded separately
under `../../correspondence/`.
The preserved certificate covers **31 named statements and 253 accepted
printed passages**, with the documented zero-order derivative repair. These
are archival counts; the new release's currently checked statement/passage
counts are recorded in `../../STATUS.md` and are not inferred from this run.

## Saved evidence replay

`03-replay-local-validator.command.json` and
`04-replay-public-ci-comparator.command.json` record successful validation of
the preserved local and CI receipts. **Neither command executes Lean.** The
local Git aliases follow the repository's unchanged `LEAN_VERIFICATION.md`;
they identify filtered public counterparts, rather than reconstructing private
repository trees.

## New Lean execution

`07-fresh-archival-lean-execution.command.json` records the separate fresh
checkpoint in the clean frozen proof worktree. All **170 commands passed**.
The unchanged frozen validator also passed; its receipt is
`12-fresh-checkpoint-validator.command.json`. The authoritative per-command
record is `fresh-lean-checkpoint/run.json`.

`fresh-lean-checkpoint.tar.gz` preserves the complete 171-file raw record in
a deterministic compressed archive. The manifest
`fresh-lean-checkpoint.bundle.json` records every member SHA-256; all members
were read back and checked. `14-final-archive-summary.json` separately
rechecks that bundle and records that tracked historical files remain
unchanged. Extract the bundle to recover the raw directory when reproducing
the frozen validator. The successful fresh run still concerns only the
qualified November 7 development.

The frozen plan contains 170 commands: the pinned Lean version, the companion
root build, `CompleteAudit`, the full top-level `SplitV4` target build, and all
top-level audit files. The Printed extension enters through `PrintedProofs`
and the aggregate dependency, correspondence, and route audits. Its nested
implementation and audit coverage are checked by the frozen validator.

The proof commit is the original alias
`92896b8a2a4099357486587d17ca1921a3dba161`, whose filtered public counterpart is
`7f515de98933646a494cca2438dac23ebf0fc2fa`. All historical source files,
manifests, manuscript files, and saved receipts remain unchanged. The archive's
integer derivative-order qualification **q ≥ 1** remains in force.

The fresh command uses `--skip-cache`: it reuses the clean, pinned Git
dependency checkouts and existing compiled dependencies, and builds missing
ones from source. It does not update dependency revisions. The Mathlib commit
is `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with Lean 4.19.0.

## Supporting cache and declaration checks

The `08`, `09b`, `10b`, and `11` command receipts concern targeted declaration
or dependency elaboration. They are useful before the full checkpoint
finishes; they are not substitutes for it. Failed attempts are retained
separately, including the initial missing-package-cache failure in `10`.

`transfer_archive_cache.py` copies only completed build artifacts after exact
Lean source-byte comparison. It writes ignored build files, never tracked
archive sources or historical receipts. `cache-transfer.json` records the
source and artifact hashes. Shared Git dependency checkouts are a local cache
optimization; mutable project build directories are not shared by symlink.

For a fresh reproduction, follow `../../../LEAN_VERIFICATION.md` and use a new,
empty evidence directory. Run the unchanged frozen validator after all 170
commands finish. The command receipts give arguments, working directories,
timestamps, exit codes, and log hashes; read them together with `run.json`.

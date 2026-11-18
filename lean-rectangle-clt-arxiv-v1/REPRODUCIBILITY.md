# Reproducing the checked intrinsic library

This project targets the frozen sources in `source-pins.json`. Its current
exported library includes the intrinsic bounded comparison, normalized
observations, concentration, smoothing, matrix estimates and C.2. A passing
run does not certify unbound printed passages or Supplemental Material G–I.

The locked dependencies require Lean 4.19.0 and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Generic chaining is pinned to
`b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc`. That repository is private:
collaborators need GitHub access to fetch it. This is a collaborator
reproduction procedure, not a publicly reproducible release. The archived
`lean-kane`, `lean-rectangle-clt-local`, and `lean-rectangle-clt-singular`
projects are sibling path dependencies in this checkout.

With the pinned toolchain on `PATH`, from this directory:

```sh
lake build
python3 tools/check_pins.py --dependencies
python3 tools/run_checkpoint.py --scope exported --require-clean --output /tmp/rectangle-fresh-run
```

Use a fresh output path. Do not run `lake update`: the committed manifest is
the dependency lock. Lake fetches its locked Git packages on the first build.
An optional mathlib build cache can accelerate that build; its absence does
not change the source requirements. Existing verified dependency build
artifacts may be reused. The checkpoint runner subsequently forces fresh
elaboration of every module in the exported import closure in dependency order, then checks
the imported chaining smoke test, chaining audit, new transitive axiom audit,
expanded mapped types, and the kernel proof-dependency graph. Its allowlist is
`propext`, `Classical.choice`, and `Quot.sound`.

Each command receives its own log and a receipt containing argv, working
directory, start/end time in UTC, exit status, and log SHA-256. `run.json`
also records the Git commit/tree, initial cleanliness, and a digest of the
checked proof sources and configuration. The runner refuses to overwrite an
existing output directory or accept source changes during execution.

The `c2` scope restricts the forced source pass to the original seven C.2
modules; `exported` is the complete current-library checkpoint. Both still
build the current root and run its audit. Historical acceptance records name
the exact proof commit and source digest they checked. The initial C.2 run
at `5c97b31` and the later combined run at `6d28758` are distinct records.

The original archive and its historical receipts remain unchanged. Saved
receipt replay, fresh archive Lean execution, and this new C.2 execution are
separate evidence scopes. See `evidence/archive-replay/` for the first two;
their success concerns the frozen November 7 development only. The source
ledger's `PASS_SOURCE_IDENTITY_ONLY` marker establishes byte identity and
exclusion bookkeeping, not mathematical correctness.

# Reproducing the checked intrinsic library

Two clean proof commits cover the [16 November paper](https://arxiv.org/abs/2611.21474v1) and its supplement. Their manuscript hashes are in [source-pins.json](source-pins.json). Lean checks 39 named results as stated and Lemma E.1 with the explicit envelope condition `A ≥ 0`. Conjecture 1 remains open. The [proof ledger](correspondence/final-coverage.json) maps all 34 explicit proof environments, including Appendices G–I, and identifies alternative derivations.

The proof of the all-threshold surface bound in Lemma H.1 uses actual facets, continuity and Fatou’s lemma. At the second proof commit the nonsimple-ridge Gauss–Green identity and the spherical conormal identity for an arbitrary number of edges were also proved separately. The latter proof uses Gaussian first moments and polar coordinates. The intrinsic bounds use the public generic-chaining proofs of Dirksen’s mixed-tail theorem and the Gaussian γ₂/expected-supremum equivalence. The lower-bound construction uses a checked scalar specialization of a foundational CLT for its Berry–Esseen estimate. [H.1 completion record](correspondence/supplemental-h-nonsimple-printed-completion.json)

Both baseline stages passed in a clean checkout of `443fbc667ed3c3ee47369e028c2c4280a5eed604`.
The [exported checkpoint](evidence/final-clean-checkpoint/run.json) completed
436 commands, including 166 registered axiom targets, 54 chaining targets,
and 168 explicit types with 10,401 project dependency nodes.
The [complete mapping](evidence/final-clean-mapping/run.json) checked
1,949 fully explicit types, forced 578 source modules, and exported
10,585 project dependency nodes. Its complete kernel axiom union is
`propext`, `Classical.choice`, and `Quot.sound`.

The immutable receipt SHA-256 digests are:

- Exported checkpoint:
  `3500c2efdb929397434a7e2201f0b203b51b14bd362d53e78666be40afb62ba5`.
- Complete mapping:
  `fe48e0e628896f8a071f078a85de65f26a7004429dc13fa49f8420f70918a610`.

Final acceptance metadata is a separate record after review and approval;
these successful proof/audit receipts do not themselves rewrite the
statement or passage registries.

The locked dependencies require Lean 4.19.0 and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Generic chaining is pinned to
`b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc`. The [pinned repository](https://github.com/VC2015/generic-chaining/tree/b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc) is public and supports anonymous HTTPS cloning. The archived
`lean-kane`, `lean-rectangle-clt-local`, and `lean-rectangle-clt-singular`
projects are sibling path dependencies in this checkout.

## Reproduce the baseline

Use two distinct checkout roles. The clean proof worktree must stay at
`443fbc667ed3c3ee47369e028c2c4280a5eed604`. The final receipt checkout is at a
later evidence/acceptance metadata commit and contains
`lean-rectangle-clt-arxiv-v1/evidence/final-clean-mapping-plan/plan.json`.
That stored plan names the proof commit and pins its exact source and ledger
bytes. It is intentionally loaded from the receipt checkout, not from inside
the proof worktree. Do not regenerate it from later acceptance metadata when
reproducing the check of the frozen proof commit.

The later acceptance metadata records the completed verification and passage
reviews; it does not change which proof commit was checked. In particular,
acceptance counts in the frozen proof checkout can predate the final
acceptance update.

Start inside a full clone of the public repository, including its archive branches, with the pinned Lean toolchain on
`PATH` and the proof commit available locally. Choose new worktree and output
paths; neither verification runner overwrites an existing output directory.
The source-ledger check reads the old V4 manuscript by its original commit ID. Enable the repository’s local Git aliases once so that the ID resolves to its public counterpart in every worktree. The example keeps all receipts and generated harnesses outside the clean
proof worktree:

```sh
set -eu
RECEIPT_REPO="$(git rev-parse --show-toplevel)"
python3 "$RECEIPT_REPO/provenance/enable-original-commit-aliases.py"
PROOF_COMMIT=443fbc667ed3c3ee47369e028c2c4280a5eed604
RUN_BASE=$(mktemp -d)
PROOF_REPO="$RUN_BASE/baseline-proof"
MAPPING_PLAN="$RECEIPT_REPO/lean-rectangle-clt-arxiv-v1/evidence/final-clean-mapping-plan/plan.json"
test -f "$MAPPING_PLAN"
git -C "$RECEIPT_REPO" worktree add --detach "$PROOF_REPO" "$PROOF_COMMIT"
cd "$PROOF_REPO/lean-rectangle-clt-arxiv-v1"
```

Prepare the locked dependencies before starting the verification runners.
An uncached checkout can fetch and build them with `lake build`; verified
build caches may also be restored. The manifest is the dependency lock:
**do not run `lake update`**. Dependency caches must retain the pinned source
identities and clean tracked Git sources. An optional mathlib build cache
changes build time, not the source requirements.

```sh
lake build
python3 tools/check_pins.py --dependencies
```

## Sequential verification

Run the exported checkpoint first. Only after it succeeds, run the mapper
from the same frozen proof worktree, using the plan from the final receipt
checkout:

```sh
python3 tools/run_checkpoint.py \
  --scope exported --require-clean \
  --output "$RUN_BASE/checkpoint"
python3 tools/prepare_full_clean_mapping.py run \
  --plan "$MAPPING_PLAN" \
  --clean-root "$PROOF_REPO/lean-rectangle-clt-arxiv-v1" \
  --out "$RUN_BASE/mapping"
```

The exported checkpoint builds the library, then forces fresh elaboration
of the ArxivV1 modules in the exported import closure in dependency order.
It installs those freshly checked artifacts before checking dependent
modules. It also runs the imported chaining smoke test and audit, the
registered transitive axiom audit, correspondence checks, explicit types,
and the kernel proof-dependency graph. The historical `c2` scope forces only
the original seven C.2 modules; use `exported` for this reproduction.

The mapper checks all 1,949 exact requested names, including numeric private
names and the checked Kane primitives. It identifies their actual imported
kernel provider modules, forces every mapped provider and the ArxivV1
Root/extra import closure, and reconciles the final provider identities.
It exports `pp.all` types and the actual project dependency graph. Its axiom
check traverses complete kernel type/proof dependencies, including Mathlib,
once over the full target union with shared visited state. A permitted
union implies a permitted axiom closure for each target. The only permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The mapper checks the actual Lean version, every manifest Git package’s
pinned commit and tracked-source cleanliness, the proof commit, source and
ledger hashes, and clean worktree status. Missing, malformed or ambiguous
mapped declarations fail the run rather than being omitted. Exact historical
non-declaration notes and method variations remain explicit in the plan.
There is no blanket exclusion of archived final-CLT dependencies: the lower
scalar specialization is disclosed, and the actual new headline routes
have separate endpoint-specific dependency checks.

Both runners record command arguments, UTC timing, exit status and log
SHA-256. The checkpoint also records each command’s working directory; the
mapper executes its child commands in `--clean-root`. The checkpoint’s
`run.json` records the checked commit/tree and source digest. The mapping
output includes
`run.json`, `expanded-types-and-dependencies.json`, `ledger-bindings.json`,
`actual-provider-bindings.json`, `forced-source-inventory.json`, and the
initial/final pinned-package identities. Verify both runners’ successful
receipts and matching immutable inputs before promoting acceptance metadata.
An exported build/audit alone does not establish every detailed passage
mapping or every printed intermediate identity.

The original archive and its historical receipts remain unchanged. Saved
receipt replay, fresh archive Lean execution and the current intrinsic proof
checkpoint are separate evidence scopes. See `evidence/archive-replay/` for
the historical November 7 checks. The source ledger’s
`PASS_SOURCE_IDENTITY_ONLY` marker establishes byte identity and exclusion
bookkeeping, not mathematical correctness.

## Reproduce the supplemental H.1 extension

After the baseline completes, keep its clean, built worktree and the shell variables above. Create a second worktree for the extension. The two cache-preparation commands check source and dependency identities before reusing artifacts from the baseline. The checkpoint then builds the whole library, directly checks 66 modules, and audits the new declarations and registered endpoints.

```sh
H1_COMMIT=63c975b7bd2176ddf559dbed1b2e087e191f7a45
H1_REPO="$RUN_BASE/h1-proof"
git -C "$RECEIPT_REPO" worktree add --detach "$H1_REPO" "$H1_COMMIT"
cd "$H1_REPO/lean-rectangle-clt-arxiv-v1"
python3 tools/prepare_verified_cache.py --from-checkout "$PROOF_REPO" --output "$RUN_BASE/h1-dependencies.json"
python3 tools/prepare_h1_verified_native_cache.py --from-clean-checkout "$PROOF_REPO" --output "$RUN_BASE/h1-native.json"
python3 tools/run_h1_printed_clean_checkpoint.py --dependency-cache-receipt "$RUN_BASE/h1-dependencies.json" --native-cache-receipt "$RUN_BASE/h1-native.json" --output "$RUN_BASE/h1-checkpoint"
```

The [saved H.1 run](evidence/supplemental-h-nonsimple-printed/clean-checkpoint/run.json) records 75 successful commands, 537 new public declaration types, and 182 registered axiom targets. Its receipt SHA-256 is `7c11133c4166d752dcf72ac2614410115601f3d5cb5170245415a08222cbb258`. Its axiom union is `propext`, `Classical.choice`, and `Quot.sound`. The full 1,949-type manuscript mapping belongs to the baseline run. The [completion record](correspondence/supplemental-h-nonsimple-printed-completion.json) links the H.1 evidence to the two printed identities.

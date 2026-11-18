# Reproducing the checked intrinsic library

The proof library is frozen at commit
`443fbc667ed3c3ee47369e028c2c4280a5eed604` and targets the manuscript sources
in `source-pins.json`. Its scope is the paper’s 40 named results: 39 as stated,
and Lemma E.1 with the explicit envelope-budget condition `A ≥ 0`.
Conjecture 1 is excluded. Detailed reading-order correspondence covers the
34 proof environments, including Supplemental Material G–I, with documented
proof-route variations.

For the source’s empty or proper full-dimensional polyhedra, H.1’s surface
bound holds at every threshold by actual facet selection and a Fatou
argument. The printed intermediate Green identity for nonsimple polyhedra
is bypassed and remains unproved; it is not claimed as a checked intermediate. The
intrinsic bounds reuse the checked generic-chaining proofs of Dirksen’s
mixed-tail theorem and the Gaussian γ₂/expected-supremum equivalence.
Lower-family scalar Berry–Esseen estimates reuse a checked scalar
specialization of a foundational CLT; this is an explicit method variation.

Both final clean verification stages passed at the frozen proof commit.
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
`b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc`. That repository is private:
collaborators need GitHub access to fetch it. This is a collaborator
reproduction procedure, not a publicly reproducible release. The archived
`lean-kane`, `lean-rectangle-clt-local`, and `lean-rectangle-clt-singular`
projects are sibling path dependencies in this checkout.

## Proof checkout and receipt checkout

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

Start inside the final receipt checkout, with the pinned Lean toolchain on
`PATH` and the proof commit available locally. Choose new worktree and output
paths; neither verification runner overwrites an existing output directory.
The example keeps all receipts and generated harnesses outside the clean
proof worktree:

```sh
set -eu
RECEIPT_REPO="$(git rev-parse --show-toplevel)"
PROOF_COMMIT=443fbc667ed3c3ee47369e028c2c4280a5eed604
PROOF_REPO=/tmp/rectangle-clt-proof-443fbc6
RUN_BASE=/tmp/rectangle-clt-final-reproduction
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

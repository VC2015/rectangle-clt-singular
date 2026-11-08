# Rechecking the independent CI evidence

The preserved independent run is [42420549190](https://github.com/VC2015/HDCLTs/actions/runs/42420549190), attempt 1, job `128547820210`. It completed successfully on **7 November 2026 at 23:55:40 UTC**. Its checked PR head was proof commit `92896b8a2a4099357486587d17ca1921a3dba161`; GitHub actually checked out synthetic merge `88b6db94075c9f3fcb8cd2d1de062ad4412da1a6`. The preserved GitHub Git-commit response verifies its parents `[e692196356de50c00fcdd66ddad0f3706db0241c, 92896b8a2a4099357486587d17ca1921a3dba161]` and tree `2b1a8ff7f82daa435e3313108bf438b35566c2eb`, exactly the proof commit's tree.

[The comparison receipt](ci-evidence-42420549190.json) checks the actual downloaded artifact, not just a workflow badge. [The independent publication-copy rerun](CI_PUBLISHED_VALIDATION.json) repeats that comparison on the committed copies. The archive is artifact `13595718284`, **10,140,737 bytes**, SHA-256 `685835b76c09cbf6b6bd4b2563a57dc60065af1f5a6e3322d010cc9eaeba727b`; the downloaded bytes match the GitHub artifact digest. The [extraction manifest](logs-ci-42420549190/extraction-manifest.json) binds all 180 raw artifact files to their ZIP members and payload hashes. [The copy manifest](CI_COPY_MANIFEST.json) records 189 publication files, including the original ZIP, complete API responses and comparison scripts; all copied bytes were checked.

The CI checkpoint passed all **170 required commands**. The pristine manuscript baseline passed all **seven required commands**, and its optional cache command also exited zero. The comparator requires exact equality of the 3,751 preserved theorem records, all 4,724 expanded records, and all 811 mapped declaration records between CI, the approved local run and the CI build log. Complete types, dependency edges and transitive axioms are compared. All 1,024 Lean sources and nine configuration files are bound to immutable proof-commit Git objects, with unchanged manuscript and historical-record hashes. Both checkpoint snapshots require clean manifest-pinned Git dependencies and the actual synthetic checkout for path dependencies.

The baseline begins with a cold dependency cache: 27 package-level Git-dependency records are exactly `(actual_revision=null, dirty=null)` before setup. They all become clean checkouts at their unchanged manifest revisions. The comparator explicitly records those initializations, requires a successful recorded cache command, and preserves dependency inventories, specifications and paths. No such initialization exception applies to either checkpoint snapshot. The pristine baseline's only untracked paths are the workflow's three cache symlinks and copied runner directory; its tracked Lean, configuration, manuscript and historical-record inputs must equal the frozen handoff commit `2bd43fd98d2a8687ccdda3745f9ac8eac96260dd` before and after execution.

The strict local proof validator is unchanged. It requires actual checkout `92896b8a2a4099357486587d17ca1921a3dba161`, so it is not applied directly to GitHub's synthetic checkout. The separate read-only comparator verifies that checkout's exact source equivalence while preserving both identities.

## Read-only comparison command

Use Python 3.12 and Git from a full repository clone containing the proof and handoff commits. From the repository root, run:

```sh
SPLIT_V4_EVIDENCE=lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension
SPLIT_V4_CI="$SPLIT_V4_EVIDENCE/logs-ci-42420549190"
python3 "$SPLIT_V4_CI/compare_evidence.py" \
  --ci "$SPLIT_V4_CI/extracted/split-v4-checkpoint" \
  --baseline "$SPLIT_V4_CI/extracted/split-v4-baseline" \
  --local "$SPLIT_V4_EVIDENCE/logs-checkpoint-92896b8" \
  --merge-metadata "$SPLIT_V4_CI/api-ci-merge-commit.json" \
  --run-metadata "$SPLIT_V4_CI/api-run-complete.json" \
  --job-metadata "$SPLIT_V4_CI/api-jobs-complete.json" \
  --check-metadata "$SPLIT_V4_CI/api-check-runs-complete.json" \
  --artifact-metadata "$SPLIT_V4_CI/api-artifact.json" \
  --archive "$SPLIT_V4_CI/split-v4-lean-command-evidence-42420549190.zip" \
  --extracted-root "$SPLIT_V4_CI/extracted" \
  --extraction-manifest "$SPLIT_V4_CI/extraction-manifest.json" \
  --local-validation "$SPLIT_V4_EVIDENCE/CHECKPOINT_VALIDATION.json" \
  --repo . \
  --output /tmp/split-v4-ci-revalidation.json
```

Choose a new output path for each comparison. This writes only the requested comparison receipt. It does not rerun Lean; the full proof-reproduction commands are in [README.md](README.md).

The published comparator SHA-256 is `3c3b1a2f244ddd4709197ae819368dc2baab702315997d086f2c429d6c1f8677`; the safe extractor SHA-256 is `be22bfa4a04076fae8d408e8ced70e9b30435722481571f854f5233657c5a7dc`. Both were independently reviewed, and the comparator was separately rerun on the actual publication copies. A later metadata-publication commit does not change the frozen proof inputs certified by this run.

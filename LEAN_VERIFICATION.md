# Archived Lean verification

The archived certificate applies to the exact **7 November 2026** manuscript, with SHA-256 `f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`. It covers 31 proved named statements and their required analytic dependencies. Conjecture 1 is excluded.

The separate printed-proof extension checks 253 valid substantive passage records. The derivative-envelope statements require integer order **q ≥ 1**; the literal order-zero reading is refuted by formal counterexamples. These qualifications are documented in the unchanged original records. The current paper's later Gaussian-width refinements and Supplemental Material G–I are outside this archived certification.

| Record | Public location |
| --- | --- |
| Frozen manuscript | [Source at the handoff](https://github.com/VC2015/rectangle-clt-singular/blob/2192ceb37f63c56e7bff1356bf7fe6bdbcf88696/research-rectangle-clt-singular/Unrestricted_CLT-split-V4.tex) |
| Result certificate | [Report](lean-rectangle-clt-singular/split-v4-certification/REPORT.md) · [PDF](lean-rectangle-clt-singular/split-v4-certification/REPORT.pdf) · [Statement map](lean-rectangle-clt-singular/split-v4-certification/statement-map.json) |
| Printed-proof extension | [Scope and reproduction record](lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/README.md) · [Correspondence review](lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/CORRESPONDENCE_REVIEW.md) · [Verification record](lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/PRINTED_PROOF_VERIFICATION.json) |
| Original local execution | [170-command ledger](lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/logs-checkpoint-92896b8/run.json) |
| Original independent CI execution | [CI comparison receipt](lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/ci-evidence-42420549190.json) · [CI evidence directory](lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/logs-ci-42420549190) |

The pinned versions are Lean 4.19.0, Lake 5.0.0-6caaee8, and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The sibling `lean-kane` and `lean-rectangle-clt-local` directories supply required Lean dependencies; their unrelated manuscripts are omitted. Do not run `lake update` when reproducing this archive.

The export changes commit and tree IDs because unrelated files are removed. Historical records retain their original IDs and URLs. The [commit map](provenance/commit-map.txt) identifies public counterparts. For the original validators, the following helper creates **local Git aliases** from original IDs to filtered public commits. It does not fetch private objects or reconstruct the full private trees.

```sh
git clone https://github.com/VC2015/rectangle-clt-singular.git
cd rectangle-clt-singular
python3 provenance/enable-original-commit-aliases.py
python3 lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/verify_record.py   --logs lean-rectangle-clt-singular/split-v4-certification/printed-proof-extension/logs-checkpoint-92896b8   --proof-commit 92896b8a2a4099357486587d17ca1921a3dba161 --validate-only
python3 provenance/recheck-public-ci-evidence.py   --output /tmp/rectangle-clt-public-ci-recheck.json
```

Use a fresh output path. These commands recheck the preserved evidence; they do not execute Lean. They passed on the public export. The public CI comparator adapts only the check of the repository-wide tree to the filtered public tree, retaining all individual source, configuration, log, dependency, declaration, artifact and original API-metadata checks. Its adaptation is explicit in the script and output receipt. The original comparator and certificate files remain unchanged.

To perform a **new Lean execution**, install the pinned Lean toolchain and enable the aliases above. Then create a clean worktree at the archived proof and choose an empty evidence directory:

```sh
git worktree add --detach ../rectangle-clt-frozen-proof   92896b8a2a4099357486587d17ca1921a3dba161
cd ../rectangle-clt-frozen-proof/lean-rectangle-clt-singular
lake --version
lake env lean --version
lake exe cache get
evidence_dir=$(mktemp -d)
python3 split-v4-certification/run.py checkpoint --skip-cache --output "$evidence_dir"
python3 split-v4-certification/printed-proof-extension/verify_record.py   --logs "$evidence_dir"   --proof-commit 92896b8a2a4099357486587d17ca1921a3dba161 --validate-only
```

The cache command obtains the pinned dependencies' optional build cache. Keep fresh execution logs separate from the original evidence. A successful reproduction concerns the frozen manuscript and does not certify later changes by itself.

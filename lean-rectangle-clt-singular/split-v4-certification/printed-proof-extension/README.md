# Printed-proof extension of the Split-V4 certificate

This development checks substantive intermediate claims and transitions in
the printed arguments of the frozen Split-V4 manuscript. It is separate from
the existing certificate of the 31 named results. That certificate and its
execution evidence are preserved unchanged.

The correspondence review accounts for all substantive in-paper arguments:
253 valid same-argument passage records and one formally refuted order-zero
reading requiring the positive-order qualification below. The local and independent-CI
170-command runs, validator and cross-run input/dependency/binding comparisons passed.
Printed-route certification is complete for every valid argument, with the derivative-envelope
claims expressly limited to integers q ≥ 1. The frozen manuscript remains unchanged;
the literal unqualified order-zero claim is not certified.

The extension proof is frozen at
[`92896b8a2a4099357486587d17ca1921a3dba161`](https://github.com/VC2015/HDCLTs/tree/92896b8a2a4099357486587d17ca1921a3dba161).
[PR #16](https://github.com/VC2015/HDCLTs/pull/16) remains unmerged. Read the
[correspondence report](CORRESPONDENCE_REVIEW.md),
[exact coverage and declaration index](coverage.json),
[verification record](PRINTED_PROOF_VERIFICATION.json), and
[portable owner-log manifest](logs-owner/manifest.json) together. Local
`/tmp/` paths retained in owner fragments describe original provenance;
downloadable copies use the manifest’s relative paths.

The frozen manuscript is
`research-rectangle-clt-singular/Unrestricted_CLT-split-V4.tex` at commit
`2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`, SHA-256
`f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`.
The original proof commit is
`69f89747f4b845491b75cb23134c056bfbcd40f7`; the result certificate and its
evidence were recorded at `69363df233f20632d73e953d09981ab495abfb50`.

New proofs are added under `RectangleCLTCompanion/SplitV4/Printed/`.
Existing alternative proofs remain available. A successful build of a new
lemma is evidence for its actual Lean contract; it does not by itself
establish complete correspondence with every printed argument.

Coverage classifications are:

- `SAME_ARGUMENT`: the printed argument, allowing routine formal adaptations.
- `ALTERNATIVE_BYPASS`: an alternative argument establishes the result while
  bypassing a substantive printed step.
- `UNVERIFIED_STEP`: the printed step has no checked formal counterpart, or
  its literal formulation is false under the stated hypotheses.

The correspondence records retain the original classification separately
from coverage supplied by the new development. Completion requires a checked
counterpart for every substantive printed argument, with any false passage
and its smallest proposed repair identified explicitly. The manuscript is
not edited by this branch.

The covariance-contraction remark’s potential, Hessian and application to
the actual probability law are checked. The cited external linear
Brascamp–Lieb consequence is proved internally using Prékopa; an independent
proof of the general Brascamp–Lieb inequality, absent from the paper, is not
claimed. Full-distance lower bounds use the conventional extended-real
liminf and equivalent eventual positive lower bounds, without an additional
boundedness hypothesis.

## Reproduction

Use a clean worktree at the frozen extension proof commit above. From
`lean-rectangle-clt-singular/`, with the pinned `lake` on `PATH`, run:

```sh
lake --version
lake env lean --version
python3 split-v4-certification/run.py checkpoint --skip-cache \
  --output /tmp/split-v4-printed-reproduction
python3 split-v4-certification/printed-proof-extension/verify_record.py \
  --logs /tmp/split-v4-printed-reproduction \
  --proof-commit 92896b8a2a4099357486587d17ca1921a3dba161 --validate-only
```

Choose a new output directory for every run. In a fresh environment,
`lake exe cache get` can fetch the optional pinned dependency cache first.
Do not run `lake update`. The checkpoint plan has 170 required commands and
directly re-executes the complete dependency, mapped-declaration and
consolidated route audits. The read-only validator checks their contracts,
source/configuration hashes, preserved evidence and fresh route assertions.

The pins are Lean `4.19.0` (compiler commit `6caaee842e94`), Lake
`5.0.0-6caaee8` and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The final isolated execution passed all 170 required commands from
22:25:16 to 23:13:33 UTC on 7 November 2026. Its
[run record](logs-checkpoint-92896b8/run.json),
[original validation](CHECKPOINT_VALIDATION.json) and
[publication-copy validation](CHECKPOINT_PUBLISHED_VALIDATION.json) are
preserved. Independent CI run [42420549190](https://github.com/VC2015/HDCLTs/actions/runs/42420549190) also passed all 170 required commands
from `2026-11-07T22:46:07.804969+00:00` to `2026-11-07T23:54:15.666455+00:00`. Its source inputs,
4,724 dependency records and 811 mapped bindings agree with the local run. The
[independent-CI comparison receipt](ci-evidence-42420549190.json), [raw CI run record](logs-ci-42420549190/extracted/split-v4-checkpoint/run.json)
and [verification record](PRINTED_PROOF_VERIFICATION.json) record the qualified completion.
The [publication-copy validation](CI_PUBLISHED_VALIDATION.json) independently repeated
the comparison on the actual published evidence and passed. The
[CI reproduction guide](CI_REPRODUCTION.md) gives the portable comparison command
and explains the cold-baseline dependency initialization.
The CI API head is `92896b8a2a4099357486587d17ca1921a3dba161`; its actual synthetic checkout
`88b6db94075c9f3fcb8cd2d1de062ad4412da1a6` has the same tree as the frozen proof.
The pristine baseline has seven successful required commands and one separately
recorded optional cache command; the checkpoint has no optional omissions.

The [copy manifest](CHECKPOINT_COPY_MANIFEST.json) records 178 verified
uncompressed originals. All 170 individual command logs and `run.json` are
raw. The duplicate aggregate stream is stored losslessly as
[CHECKPOINT_RUNNER.log.gz](CHECKPOINT_RUNNER.log.gz); the
[archive manifest](CHECKPOINT_ARCHIVE_MANIFEST.json) records the original and
stored hashes and explains the historical copy-manifest paths.

## Positive derivative order in Appendix A

The local derivative-envelope claim at frozen TeX lines 1848–1852 and its
averaged version at 1872–1877 should say **“for each integer q ≥ 1.”** The
printed context concerns higher derivatives, but the displayed claims do
not explicitly exclude zero. The formal development proves every positive
order. At order zero, the one-face centered Gaussian smoother at threshold
zero has expectation exactly 1/2 for every positive bandwidth. A finite
signed-face example also fits the full rectangle family: for p=1, normals
+1 and -1 and box [-1,1], the smoother is at least 1/3 on |G|≤1, so its
expectation has a fixed positive lower bound for every positive bandwidth.
Both contradict a uniform upper bound tending to zero with the bandwidth.
These counterexamples are checked in `Printed/EnvelopeZeroOrder.lean` and
`Printed/EnvelopeZeroOrderSigned.lean`.

The [exact proposed wording](PROPOSED_MANUSCRIPT_REPAIR.md) is provided for
the editorial branch. This is a proposed editorial repair. The frozen manuscript, its original
certificate and tag, and Yuta’s and Denis’s revisions remain separate. After
editorial integration, identify the new manuscript commit and hash, compare
every affected hypothesis, display, proof transition and declaration, update
the correspondence map, and rerun the pinned builds and transitive axiom
audits before certifying the revised text.

## Preserved certified snapshot

PR [#14](https://github.com/VC2015/HDCLTs/pull/14) was merged with a merge
commit after final report-head CI passed. The annotated tag
[`split-v4-lean-certified-2026-11-07`](https://github.com/VC2015/HDCLTs/tree/split-v4-lean-certified-2026-11-07)
points to `e692196356de50c00fcdd66ddad0f3706db0241c`.
The report is available as
[Markdown](https://github.com/VC2015/HDCLTs/blob/split-v4-lean-certified-2026-11-07/lean-rectangle-clt-singular/split-v4-certification/REPORT.md)
and [PDF](https://github.com/VC2015/HDCLTs/blob/split-v4-lean-certified-2026-11-07/lean-rectangle-clt-singular/split-v4-certification/REPORT.pdf).
The [publication receipt](PRESERVED_CERTIFICATE.json) records the merge
parents, annotated tag object, successful final CI, exact hashes and
exclusion of PR #15. This printed-proof extension is not part of that tag.

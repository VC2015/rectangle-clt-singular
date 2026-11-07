# Printed-proof extension of the Split-V4 certificate

This development checks substantive intermediate claims and transitions in
the printed arguments of the frozen Split-V4 manuscript. It is separate from
the existing certificate of the 31 named results. That certificate and its
execution evidence are preserved unchanged.

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

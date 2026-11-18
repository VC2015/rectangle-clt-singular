# Supplemental H.2 Gaussian inequalities

`RectangleCLTArxivV1/SupplementalHLinearGrowth.lean` checks both conclusions
of Lemma H.2 from the frozen supplement at source commit
`1803366cc994d9facae8e128ee180f68e319486f`, lines 1304–1326.
The supplement source SHA-256 is
`5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb`.

The public endpoints are:

- `RectangleCLTArxivV1.lemma_H2_gaussian_matrix`: the actual normalized
  covariance satisfies `I - K_w` positive semidefinite, and the actual
  unnormalized Gaussian second-score matrix satisfies the nuclear bound.
  The hypotheses are nonnegative measurable log-concavity, positive finite
  Gaussian mass, and a finite weighted squared-norm moment. Thus the proof
  covers the printed linear growth class and is stronger because the
  linear growth assumption is unnecessary.
- `RectangleCLTArxivV1.lemma_H2_projected_reference`: the actual weighted
  Gaussian mean satisfies the relative projected reference inequality for
  a symmetric idempotent matrix `P` and any nonnegative measurable
  reference `β(Pg)` with finite Gaussian mass. The weight has positive
  finite mass and a finite weighted squared-norm moment. No boundedness
  or log-concavity of the reference is required.

The Gaussian law is the actual finite product standard normal law.
`weightMean`, `weightCovariance` and `weightedScore` are the archived
integral definitions; none of the desired estimates is a premise. The
symmetric nuclear norm is the archived trace-dual nuclear norm on real
symmetric matrices.

## Proof route and correspondence limit

The proof uses increasing upper caps `min(w,n+1)`. It proves, rather than
assumes, that capping preserves multiplicative log-concavity and positive
Gaussian mass. The bounded Prékopa covariance contraction is inherited
from the checked archive. Ordinary Gaussian coordinate moments follow
from the finite weighted squared-norm moment; dominated convergence
passes the normalized covariance, the nuclear norm and all terms on the
right side to their actual limits.

The relative reference inequality caps both `w` and `β` by the same
constant. Capping preserves the reference comparison pointwise. The
bounded reference proof is the separately checked projected-mean proof;
ordinary dominated convergence and continuity of `log` at the strictly
positive mass ratio remove the cap. Its exponential tilt identity uses
Gaussian translation, an equivalent route to the printed independence
of projected and orthogonal Gaussian components.

This proves the complete mathematical statement of H.2, but records an
explicit proof-route difference from the printed direct differentiation
of the unbounded Gaussian convolution. It does not certify those exact
unbounded differentiation passages, the localized Hausdorff surface
comparison in H.1, the cubic/two-face propositions, or the full release.

## Reproduction

With the pinned Lean toolchain on PATH, run from the new project:

```
python3 evidence/supplemental-h-gaussian/run_checkpoint.py
```

`run.json` records the actual build, a forced source compilation, and a
strict transitive axiom audit of all eleven new theorems. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. It hashes all new-project
transitive sources and verifies that they stayed unchanged during the
checkpoint. Imported historical source files and archival receipts are
not edited by this work.

# Split-V4 proof status and open obligations

The frozen proof checkpoint is `7bf2325`. Twenty-one of the 31 proved named
statements are checked; ten remain pending in this snapshot. The whole
manuscript is not certified. Conjecture 1 is excluded and is never an assumption.
Later work is outside this receipt until it has its own frozen build.

The exact declarations, expanded types, source context and kernel dependencies
are in [statement-map.json](statement-map.json) and
[dependency-map.json](dependency-map.json). The
[verification record](../SPLIT_V4_VERIFICATION.json) records all 119 successful
commands, 2,750 dependency records, and the strict audit of 4,756 imported
companion theorem declarations. A fresh pristine baseline passed all eight
handoff commands in GitHub CI run `42398843876`.

The target is handoff commit `2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`, with
manuscript SHA-256
`f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`.
The manuscript and frozen October verification records are unchanged. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted transitively.
Statement completion and the manuscript proof route are recorded separately.

## Checked statements

- Corollaries 1–2, Theorems 2–3, Propositions 2–3, and Lemmas 1–2.
- Theorem 4: the actual symmetric bounded construction, exact orthant constant
  `1/(8*exp 1)`, and the full rectangle-distance lower conclusion.
- Lemmas B.3–B.5: actual Gaussian mean; logistic nuclear-norm estimate with a
  constant chosen before all models, every tuple length and zero noise;
  actual averaged hard Gaussian threshold derivative with generic base
  concentration, including the facet/ridge cancellation used in the proof.
- Lemma C.1, Lemma E.1, Lemmas F.1–F.3, and Lemmas G.1–G.4.

All upper bounds retain their actual probability classes, exact Gaussian
covariance and singular cases. Polynomial bounds retain the separate fourth
moment condition for `2 < q < 4`, constants depending only on fixed `q`, and
the literal supremum over the full array class. F.1 permits independent
nonidentical scalar laws and strict tails including atoms at zero. F.3 proves
the actual masked symmetric finite-product model, moments, rank and gap.

The cube proof handles ties directly using selected supporting branches.
G.2 uses a proved good-clock cutoff in place of the printed expected-clock
width step. These route distinctions are explicit in the statement map.

## Relative theorem and analytic chain: five pending statements

Theorem 1 (`thm:unrestricted`), Proposition 1 (`an:prop:derivative`),
Lemma A.1 (`appx-lem:envelope`), and Lemmas B.1–B.2
(`appx-an:lem:identity`, `appx-an:lem:restoration`) remain pending here.

The existing `unrestrictedCLT` proves the envelope specialization and has no
relative `s4` parameter. The checked relative moment helpers retain signed
cubic aggregation and both distinct fourth matrices, derive third bounds
from fourth-only admissibility, and transfer the exact matrices through face
maps without positive eigenvalue assumptions.

The calibrated FaceSmoother seeded identity and arbitrary-amplitude finite
mask differentiation are checked components. The remaining B.1 contract
requires the full ordinary bounded-derivative C4 test class and literal
fourth-order kernels. B.2 still requires the final conditional original-space
contract with joint auxiliary dependence, signed zero-shift refinement and
both squared-face fourth budgets. A.1 still requires all positive derivative
orders and the actual translated supremum with genuine integrability.

Proposition 1 must assemble these actual estimates along the initial Slepian
and seeded paths, preserve the generic concentration constant, and justify
time integration with `epsilon=L*h^2`. Theorem 1 must then optimize to
`C*min(1,L^(3/2)*(delta+sqrt(s4*D_L)))`, retaining `s4` throughout.

## Polyhedral transfer: one pending statement

Corollary 3 (`cor:polyhedral-transfer`) remains pending only through the
relative-moment endpoint of Theorem 1. Actual Gaussian pushforward, bounded,
Orlicz and polynomial final bounds are checked. The polynomial transfer
proves `B -> J^2*B`; exact zero-variance face deletion includes negative
thresholds and empty face families. The relative branch must retain
`delta -> J*delta` and `s4 -> J^2*s4`.

## Lower calibrations: four pending statements

Theorems 5–8 (`opt:q4-lower`, `opt:q4-growing`, `lower:dense`, `lower:sparse`)
remain pending in this snapshot. F.1–F.3 and the genuine Gaussian extreme
value helpers are checked inputs. The final calibrations must prove eventual
parameter validity, rounded mask coverage, negligible remainders, and full
rectangle-distance lower conclusions under the exact growth assumptions.
Fixed `B` and growing `B_n` must remain distinct, and Theorems 5 and 7 must
include the actual class supremum conclusions.

## Evidence policy

Every certified entry requires an expanded actual Lean type, a successful
frozen source build, and its permitted transitive axiom closure. A helper's
compilation is not whole-statement completion. The excluded conjecture is
never a premise. The original October records remain unchanged, and previous
partial checkpoints are retained under `checkpoints/`.

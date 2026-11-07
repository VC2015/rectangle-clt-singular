# Split-V4 statement and proof correspondence

This review concerns the exact handoff at
`2bd43fd98d2a8687ccdda3745f9ac8eac96260dd` and complete Lean proof source
`69f89747f4b845491b75cb23134c056bfbcd40f7`. Execution outcomes, source
fingerprints, expanded endpoint types and axiom closures are recorded in
[the verification record](../SPLIT_V4_VERIFICATION.json),
[statement-map.json](statement-map.json), and
[dependency-map.json](dependency-map.json).

The inventory contains 31 proved statements and one excluded conjecture.
The conjecture is never an assumption. The manuscript, its magenta markings,
the analytic audit, the three October verification records, and the pinned
Lean 4.19.0/mathlib versions are preserved.

## Relative theorem and analytic chain

`relativeFourthMomentCLT` accepts the actual bounded independent array,
unit marginal covariance and both distinct fourth-moment matrix bounds.
It derives the signed third budget from the bounded array. Its conclusion
uses the full measurable rectangle distance and the paper's relative rate.
`relativeEnvelopeCLT` gives the envelope specialization with the same fixed
universal constant. Neither endpoint assumes a comparison or derivative
estimate, a positive eigenvalue, or a correlation gap.

`proposition_relative_derivatives` fixes the bandwidth and comparison
constants before dimensions, probability models, thresholds and relative
budgets. Its expanded contract includes the actual initial Slepian cubic
and fourth remainder, the threshold supremum defining the initialization
error, the normalized seeded derivative identity, and both seeded estimates.
The signed cubic tensor is aggregated before taking its absolute value.
Both the initial and seeded time integrals use proved endpoint continuity
and genuine integrability.

The general B.1 endpoint uses an ordinary `ContDiff` test function with
genuine global bounds on derivatives one through four. It allows a
linearly growing test value, arbitrary positive C1 amplitude with valid
Bernoulli retention, and the actual independent Gaussian seed. The third
tensor is the literal sum over ordered coordinate triples. The three fourth
kernels use the manuscript's ordinary derivative slots; their symmetry is
proved for C4 functions.

B.2 uses bounded-indicator conditional factorization on the joint auxiliary
array. The auxiliaries may depend on one another and on the conditioning
field. The Gaussian is independent of that field, and base concentration is
unconditional. There is no standard-Borel hypothesis on the ambient space.
Explicit second-moment integrability gives genuine conditional matrix
moments. The signed zero-shift refinement and both squared-face fourth
budgets are retained; a separate wrapper also allows almost-everywhere
zero shifts. Singular whitening uses the support projection inequality.

B.3 proves the actual Gaussian mean through entropy and one-face
factorization. B.5 proves the actual averaged hard Gaussian threshold
derivative, with the generic concentration constant and the localized
facet/ridge cancellation. B.4 assembles the actual nuclear-norm estimate,
regularization, padding and limit arguments. Its constant precedes models
and tuple lengths; repeated normals, singular covariance and zero noise
are included.

A.1 includes every positive derivative order. It proves measurability and
integrability of the genuine translated supremum over the face seminorm
ball, including unbounded seminorm balls. Its concrete model constructors
contain actual independent bounded or Gaussian components, with no assumed
boundary or derivative estimate.

## Polynomial comparison and face transfer

The polynomial upper endpoints retain the actual conditional truncation
laws and the separate coordinate fourth-moment condition even when
`2 < q < 4`. They include the literal supremum over the full array class,
with constants depending only on fixed `q`. The Bennett route uses the
proved G.1 comparison and G.4 maximum estimate.

G.1 retains both conditional matrix fluctuation and large-increment mean,
the actual expected maximum remainder, and all five terms. Its common-point
fourth contraction is proved before Gaussian averaging. G.3 has actual
copy averages and conditional expectations, without a symmetry or
zero-skewness assumption. The three time integrals and endpoint limits are
proved.

The relative face transfer applies the actual standardized linear map and
matches the Gaussian pushforward covariance. Both fourth matrices undergo
`s4 -> J^2*s4`, and the envelope undergoes `delta -> J*delta`. The logarithm
is recomputed for the retained face count. Bounded, Orlicz and polynomial
branches are also checked, including `B -> J^2*B`. Zero-variance faces can
be deleted under both laws, including negative thresholds and the all-zero
case.

## Lower constructions and constants

The finite-product common family has actual i.i.d. centrally symmetric
observations, matching Gaussian covariance, moment and envelope bounds,
rank and correlation gap. The moderate-tail input allows independent
nonidentical scalar laws and strict tails with atoms. The shift comparison
uses the stated signed shifts and actual independence.

The bounded, fourth-moment and growing-fourth constructions retain the
paper's respective lower constants `1/(8*exp 1)`,
`1/(2*sqrt 2*exp 1)` and `1/(4*exp 1)`. Full-distance lower conclusions use
the extended-real liminf, so no unproved boundedness premise is added to a
real-valued liminf. Fixed and growing envelopes remain distinct.

The dense and sparse constructions retain the exact rates and original
growth hypotheses. The sparse proof derives its internal mask scale and
rounded coverage from the paper's `K`, `log(K)/L` and rate assumptions.
It derives disappearance of the coordinate contribution from `K -> infinity`.
Parameter fallbacks affect only finitely many indices and are transported
by eventual equality.

`UniformLowerConstants.lean` makes the constant order literal: Theorem 5
chooses an absolute lower constant before `B` and all dimension sequences;
Theorem 7 chooses its upper constant before `B` and its lower constant
before all sequences; Theorem 8 chooses both constants as functions of `q`
before the envelope and dimension sequences. The conclusions compare the
actual lower model, the symmetric class supremum and the unrestricted class
supremum. Coordinate duplication preserves the full rectangle distance and
provides correlation gap zero.

## Explicit proof-route variants

| Statement | Checked formal route |
| --- | --- |
| Corollary 1 | The printed normalization, with the historical split-matrix bounded CLT as its input. |
| Corollary 2 | Clipping, L2 control and block-Gaussian covariance restoration; exponential admissibility is obtained at `2K` and absorbed by the universal constant. |
| Lemma 2 | Deterministic common-threshold telescoping and an atom-safe endpoint transfer replace the printed random-displacement argument. |
| Theorem 3 | The actual two-point model uses a specialized proved Esscher/Cramer tail bound, followed by the stated Gaussian-maximum and product asymptotics. |
| Lemma B.3 | The substantive entropy/face proof is followed; supporting tangents implement Jensen and Cameron-Martin translation proves the exact one-face factorization. |
| Lemma C.1 | Direct selected supporting branches handle ties and zero coefficients in the uniform-cube boundary argument. |
| Lemma G.2 | A proved good-clock cutoff replaces the printed expected-clock-width step. |

The revised relative, conditional, threshold, matrix and large-increment
chains have their own formal endpoints and evidence. Reusing a historical
endpoint for one of the rows above does not stand in for those chains.

## Axiom and execution checks

The strict allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
The dependency extractor reads the checked kernel environment, records
actual types and direct type/proof edges, and computes each declaration's
exact transitive axiom set. Its graph cases match Lean 4.19's official
collector; reverse reachability handles cycles. The graph's axiom union is
cross-checked with that collector. The optimized implementation was also
independently compared record by record with the original collector on all
1,684 declarations in the frozen eighteen-statement checkpoint.

The complete certificate requires a fresh isolated run, all intended build
and audit commands, a recorded complete imported-theorem audit, unchanged
proof inputs, clean pinned Git dependencies before and after execution,
every expanded contract, and all required helper declarations. The receipt
generator rejects incomplete statement sets and constant-order fallbacks
when issuing a complete certificate.

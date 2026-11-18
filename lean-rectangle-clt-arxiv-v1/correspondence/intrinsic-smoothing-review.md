# Intrinsic derivative and smoothing proof notes

Scope: supporting endpoints for A.1, B.3, B.4 and Lemma 2 in the frozen
16 November main source. This note does not certify the full statements
until the actual concentration suppliers and passage mapping are checked.

* `integral_logisticEnvelope_intrinsic` now uses the literal common-threshold
  differential route in `EnvelopeThresholdIntegration.lean`: the derivative
  of `F_s`, the derivative of `log(F_s(1-F_s))`, its integral from zero to
  `s`, and the integral of `F_s'` over `[-h,h]`. This gives the exact printed
  comparison with coefficient `exp 1/2`, before conditioning on the shared
  exponential clocks and applying the width-`h` layer premise. The final
  public constant remains `4*C0*h*κ`. Earlier checkpoints recorded an
  alternative `h*log 2` comparison; the new printed checkpoint supersedes
  that proof body.
* `averaged_translated_derivative_intrinsic` integrates the proved local
  logistic derivative envelope. The derivative order is positive, the
  supremum is the genuine measurable translated supremum, and the product
  of fixed projected direction norms remains outside the expectation.
  `intrinsicDerivative_inverse_power_eq_rpow` identifies the denominator
  with the paper's real power.
* `gaussian_mean_relative_to_single_face` is the actual B.3 Gaussian mean
  inequality, using bounded measurable weights and positive masses. Its
  statement environment is the unique verbatim match in the historical
  statement comparison. Its proof now explicitly assembles weighted Jensen,
  the printed orthogonal-coordinate independence factorization, the
  tangent mean identities, and weighted Cauchy–Schwarz. The printed B.3
  checkpoint checks these six actual direct proof dependencies and rejects
  a call to the earlier final Gaussian entropy endpoint.
* `selector_nuclear_bound_intrinsic_paper` is the actual Gaussian score
  nuclear-norm integral for the signed coordinate face system used in the
  paper's global setup (`m=2p`, rows `+A_j,-A_j`). Inactive faces contribute
  zero. It retains the genuine concentration premise and all original
  bandwidth and Gaussian scale conditions. The archived theorem permits
  any positive concentration constant, so substituting
  `C=C0*κ/sqrt L` is legitimate. The fixed `C0` is absorbed into
  `(logisticMatrixConstant*max 1 C0)^(k+1)`; `κ` remains linear.
  The support-coordinate counterpart `logistic_matrix_estimate_intrinsic`
  explicitly requires the complete signed normals and their actual
  opposite map, supplied by the global setup `u_(p+j)=-u_j`. These are
  the signed rectangle specializations used in the comparison proof.
  The archived nuclear reduction,
  covariance contraction, threshold estimate, padding and limit proofs
  remain actual proof dependencies.
* `averagedSelectorMatrixEstimate_intrinsic` turns that nuclear estimate
  into the genuine measurable signed-trace dual interface. It assumes no
  trace, derivative or matrix conclusion.
* `rectangleDistance_le_smoothingDiscrepancy_intrinsic` proves
  `ρ ≤ M_h + 9*C0*h*κ*L` from actual intrinsic concentration of both endpoint
  laws. It uses the literal threshold sandwich, shared random radius,
  Jensen and the radius expectation from `Printed.EndpointMixture` and
  `Printed.ClockMean`. A zero-width layer is empty, so no atom assumption
  is inserted. Closed boxes are extended to all measurable coordinate
  rectangles by the archive's atom-safe limit theorem. The actual bounded
  and Gaussian endpoint concentration suppliers are separate dependencies
  that must be discharged before calling this a completed Lemma 2.

Fresh build, source hashes, exact commands, UTC times, theorem types and
14-declaration axiom audit are in
`evidence/intrinsic-smoothing/checkpoint-3/`. The allowed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

## Direct initialization envelope

`DirectIntrinsicEnvelope.lean` discharges the actual Slepian envelope
premise from the original centered independent bounded array and its
covariance factor. For times at most one half, the bounded component has
variance at least one half; conditioning on the Gaussian component and
using the printed C.1 bound gives `512*h*E||W||`. For the remaining times,
the Gaussian component supplies `8*h*gΣ`. Combining this intrinsic estimate
with the existing logarithmic envelope bound gives the exact minimum
coefficient `κ` with the archived coefficient `4096`. Both time endpoints
are included. No boundary, derivative, smooth comparison or final CLT
estimate is assumed in this endpoint. The intrinsic component averaging now uses the same literal width-`h`
comparison as A.1. The separate logarithmic envelope estimate remains a
reused proved archive estimate; it is combined with the intrinsic branch
only when taking the minimum coefficient.

Latest checks for these additions are in
`evidence/intrinsic-smoothing/direct-envelope-2/` and
`evidence/intrinsic-smoothing/b3-printed/`; the earlier numbered checkpoint
records the prior version before the explicit B.3 assembly.

The current literal A.1 and direct-envelope proof bodies are checked in
`evidence/intrinsic-smoothing/a1-printed/`. That route audit checks the
actual proof edges through both fundamental-theorem integrations. Earlier
checkpoints remain historical checks of their recorded source hashes.

# Split-V4 open proof obligations

Validation checkpoint: all newly proposed split-V4 proof modules are awaiting
fresh compilation, expanded-type inspection, and transitive axiom audits.
Their presence in the checkout is not a successful Lean check. The source
correspondences below are provisional until those checks are recorded. This
report does not change any inventory entry to certified.

The target is repository commit
`2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`, with manuscript SHA-256
`f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`.
The authoritative source includes the definitions and assumptions before
each named environment. [statement-map.json](statement-map.json) contains
the source excerpts, candidate declarations, and per-entry obligations.
The October verification records remain historical evidence.

There are 31 proved statement targets. Conjecture 1
(`conj:sharp-unrestricted`) is excluded from certification and may not be
used as an assumption. The groups below cover all 31 targets exactly once.

## Appendix B: relative moments and the seeded proof

Targets: Theorem 1 (`thm:unrestricted`), Proposition 1
(`an:prop:derivative`), Lemma A.1 (`appx-lem:envelope`), and Lemmas B.1–B.5
(`appx-an:lem:identity`, `appx-an:lem:restoration`, `appx-an:lem:mean`,
`appx-an:lem:matrix`, `appx-an:lem:threshold`).

The existing `RectangleCLT.Companion.unrestrictedCLT` is a candidate for
the envelope specialization of Theorem 1. Its type has no `s4` parameter.
It does not supply the relative fourth-moment conclusion
`C min(1, L^(3/2) (delta + sqrt(s4 D_L)))`, or certify the revised proof
route by itself.

Proposed components are in [RelativeMoments.lean](../RectangleCLTCompanion/SplitV4/RelativeMoments.lean)
and [SeedCalibration.lean](../RectangleCLTCompanion/SplitV4/SeedCalibration.lean).
The former defines signed cubic and two distinct fourth-moment matrices,
includes genuine entrywise integrability, identifies the fresh-copy matrix
with a product-law integral, and proposes envelope consequences. The latter
proposes the calibrated moment identities, signed-density moments, and
kernel calculations. These components still need the analytic assembly:

1. For Lemma B.1, construct the actual masked Gaussian path for arbitrary
   positive `C1` scale `gamma`, with `varpi=(1-t)/gamma^2` in `[0,1]`.
   Prove its expectation derivative with exactly the displayed `a_t`,
   `b_t`, and `c_t` kernels. Preserve the signed aggregate third tensor
   before taking bounds. The calibrated identities
   `varpi*gamma^2=1-t`, `varpi*gamma^3=1-t^2`, and the cubic coefficient
   `-t/3` are algebraic inputs to this identity, rather than its proof.
2. For Lemma B.2, prove the translated-base restoration estimate from
   actual conditional matrix budgets and conditional Gaussian independence.
   Keep `Q_j <= s4*Sigma` and `Qtilde_j <= s4*Sigma` separately: same-copy
   and independent-copy products occur in different terms. Establish the
   signed `s=1` refinement at zero translation and both `s=2` squared-face
   budgets. The arrays may depend on the conditioning sigma-field and on
   one another; mutual array independence is not an available hypothesis.
3. Lemma B.3 has a historical weighted-Gaussian-mean candidate. Expand
   `weightMass`, `weightMean`, `vectorNormSq`, and the face contraction,
   then check the positive masses and the precise entropy inequality.
   Fresh imports and axiom closure are still required.
4. For Lemma B.5, define the actual averaged threshold derivative and
   prove `E |D(b(V0))| <= C (sigma L^(3/2) + delta L^2)` first for
   independent unit normals. The missing geometric step is the written
   disjoint interval/normal-sector argument with cancellation of the
   near-parallel angular factor. Prove the regularization limit for repeated
   or dependent normals and singular covariance. An older signed-surface
   estimate does not discharge this revised threshold argument.
5. Derive Lemma B.4's nuclear-norm sum over every ordered face tuple from
   B.3, B.5, and the logistic selector tilt. Keep the dependence on the
   generic concentration constant until the actual application fixes it.
   Historical Prékopa and selector-contraction modules are reuse candidates
   whose expanded contracts and axiom closures must be checked.
6. Match Lemma A.1's arbitrary face norm and derivative supremum over
   translated points, then propagate the moment budgets through Proposition
   1. Separate the initial Slepian step from the seeded path, integrate
   `t/(t+epsilon)` and `(t+epsilon)^(-1)` with `epsilon=L*h^2`, and retain
   the endpoint cost of order `delta*L^(3/2)`. Assemble the relative rate
   without replacing `s4` by `delta^2` before the refinement is proved.

## Appendix C: intrinsic anti-concentration

Targets: Lemma 1 (`lem:concentration`) and Lemma C.1
(`appx-lem:cube-boundary`).

The historical `bounded_boundary_concentration` and
`gaussian_boundary_probability_le` provide logarithmic-dimension
specializations for coordinate faces. They do not contain the intrinsic
expected face maximum required by the current statements.

The smallest missing boundary input is Lemma C.1's actual cube inequality
`P(t <= F(epsilon) <= t+h) <= (h+8b)*M/sigma^2`, where
`M=E max(0,max_alpha b_alpha dot epsilon)`. It must hold for every `h>=0`
and threshold, followed by its separate `sqrt(2 log(m+1))` consequence.
To obtain Lemma 1, formalize the conditional Rademacher argument, the
squared-coefficient contraction, and control of small random conditional
variances by the same expected maximum. Prove the direct Gaussian
intrinsic bound as well. A proof of only a `sqrt(log p)` estimate leaves
both intrinsic conclusions open.

## Appendix G: paired comparison and Bennett refinement

Targets: Lemmas G.1–G.4 (`ben:comparison`, `ben:smoothing`,
`ben:paired-interpolation`, `ben:maximum`) and Proposition 3 (`poly:bennett`).

[PairedExchange.lean](../RectangleCLTCompanion/SplitV4/PairedExchange.lean)
proposes a scalar trapezoidal identity proved by FTC, cutoff-preserving
copy exchange, odd and even endpoint integral pairings with genuine
integrability, and the scalar coefficient `-s/8`.
[TimeWeights.lean](../RectangleCLTCompanion/SplitV4/TimeWeights.lean)
proposes integrability, endpoint limits, and the three time integrals
`2`, `pi`, and `4/3`. These are ingredients of the comparison proof.

For G.2, the remaining smoothing input must apply to every measurable
vector `V`, without a boundedness or moment assumption on `V`. Prove the
Gaussian-endpoint absorption using the logistic mixture and the Gaussian
shell estimate, then extend to the full rectangle class. The bounded-array
smoothing proposal in `Smoothing.lean` does not have this contract.

For G.3, construct all copies on actual product probability spaces and
differentiate the Slepian expectation for finite-moment summands. Supply
Gaussian integration by parts through a covariance factor, allowing
singular covariance. Transfer the scalar trapezoidal identity to vector
directional derivatives, justify the integral exchanges, and condition on
the original array. In the resulting identity, `b_h` and `T_h` must be the
actual conditional large-increment mean and truncated covariance, and
both `b_h` and `T_h-Sigma` must remain present. Copy exchange supplies
the sign reversal on the truncation event; no zero-skewness assumption is
available or needed for that step.

For G.1, prove the fourth-derivative common-point contraction before
Gaussian averaging. It must retain the maximum of coordinate fourth-moment
sums. Bound the conditional matrix fluctuation and conditional
large-increment mean; then integrate the paired identity using the time
weights and justified endpoint limits. The resulting estimate must retain
both `v_t` and `M_t`. Importing CCKK Lemma A.1 as an unproved premise would
leave the required self-contained proof open.

For G.4, prove and integrate the truncated symmetric-coordinate Bennett
tail inequality for every `q>1`, giving the stated logarithmic denominator
and the `A^q/u^(q-1)` remainder. Prove the `v=0` almost-sure-zero case and
genuine integrability of the expected maximum. Apply G.1 and G.4 to
Proposition 3, prove `K_q=(V_q/U)^2`, and optimize both `K_q<=1` and
`K_q>1` regimes with constants depending only on fixed `q`.

## Appendix E: conditional truncation and polynomial assembly

Targets: Lemma E.1 (`lem:maximum`), Proposition 2 (`poly:transfer`), and
Theorem 2 (`thm:polynomial`).

Prove Lemma E.1's expected-maximum bound from genuine coordinate variance
and `q`-envelope moments, for independent centered vectors and `q>2`.
Conditional truncation then needs the actual conditional distributions,
centering, measurability, independence, and entrywise covariance control.
It is not enough to postulate a truncated vector with the desired moments.

There is a precise mismatch in the available Gaussian comparison APIs.
`RectangleCLT.gaussianComparisonFull` requires
`0 < pairGap(reference covariance)`, while
`RectangleCLT.gaussianComparisonGlobal` requires
`0 < fullEigenvalue(reference covariance)`. Appendix E permits singular
covariance and zero correlation gap. The missing import or new theorem
must instead provide the Gaussian-to-Gaussian rectangle comparison
`C min(1,L*sqrt(Delta))`, with only the written lower marginal-variance
bound and `Delta` the entrywise covariance discrepancy. This dependency
is distinct from G.1's matching-covariance comparison.

Define the exact measurable array classes with genuine moment
integrability, retain the coordinate fourth-moment condition even for
`2<q<4`, and prove the uniform bounds of Propositions 2 and 3. Assemble
their minimum in Theorem 2, including saturation by one, the case `q=4`,
and all small/large parameter regimes. Express the supremum over the paper's
array class, or prove equivalence with an exact uniform formulation.
Choose constants before dimensions and probability models; only the
permitted dependence on fixed `q` may remain.

## Transfers and smoothing

Targets: Corollaries 1–3 (`cor:observations`, `cor:subexponential`,
`cor:polyhedral-transfer`) and Lemma 2 (`lem:endpoint`).

Proposed endpoints in `ObservationNormalization.lean`,
`SubexponentialTransfer.lean`, and `Smoothing.lean` use the actual supremum
rectangle distance and choose constants before the probability model.
Check their expanded types against the exact rates and normalize average
marginal second moments into the covariance of the normalized sum.
For Corollary 2, check the genuine Orlicz definition and its integrable
exponential-moment bridge; the Gaussian restoration must preserve the
cross-covariance blocks of the clipped and residual vectors. Lemma 2's
proposed reuse follows the older endpoint proof, so statement correspondence
and the current proof route must be recorded separately.

`PolyhedralGeometry.lean` proposes the standardized face-map membership
equivalence, unit face covariance diagonal, bounded-array projection, and
deterministic envelope and weighted-moment inequalities. Corollary 3 still
needs the actual probability/Gaussian pushforward correspondence and all
moment-class transfers. Verify the substitutions `delta -> J*delta`,
`s4 -> J^2*s4`, `K -> J*K`, and `B -> J^2*B`, as well as the dimension
logarithm. Treat zero-variance faces according to the paper's contract;
do not add a covariance rank, eigenvalue, or correlation-gap assumption.

## Appendix F: lower constructions and calibrations

Targets: Theorems 3–8 (`opt:skew-lower`, `opt:symmetric-lower`,
`opt:q4-lower`, `opt:q4-growing`, `lower:dense`, `lower:sparse`) and Lemmas
F.1–F.3 (`opt:moderate-tail`, `lower:shift-comparison`,
`lower:family-properties`).

Theorem 3 has the historical candidate `skewedTwoPointLowerScale`.
Check growing `B_n` quantifiers, attained envelope, full rectangle
distance, and the constant `sqrt(2)/(4*exp(1))` by a fresh expanded-type
and axiom audit. This candidate does not certify the new symmetric laws.

For Lemma F.1, extend the tilted-law calculation to arbitrary independent,
possibly nonidentically distributed bounded scalar summands with total
variance one. Existing `LowerTiltedBerryEsseen` and Cramér-tail modules
instantiate a specific two-point law. Their existence alone does not
establish the general moderate-tail contract. A proved scalar
Berry–Esseen input may be reused, but the arbitrary tilted product laws,
strict tail, and uniform error through atoms/lattices still need proof.

For F.2, prove the CDF convolution/Taylor estimate with the signed leading
term `F'(t)*(E V-E U)`. Allow noncentered shifts with finite second moments
and only the two stated independence relations. Centered shifts or a
stronger joint independence assumption would not match its application.

For F.3, construct the actual common symmetric finite-product law and prove
iid observations, central symmetry, centering, unit marginal variances,
the full covariance, rank `2*m-1`, correlation gap `v`, exact fourth
moments, and the stated `q`-envelope bound. Establish genuine integrability
and attainment of the maxima used by the calibrations.

Then prove eventual validity of every mask probability and both remainder
estimates under the exact growth conditions. The unmasked and masked
calibrations have opposite leading discrepancy signs. Keep fixed `B`
separate from growing `B_n`. Check the constants `1/(8e)`,
`1/(2*sqrt(2)*e)`, and `1/(4e)` in Theorems 4, 5, and 6 respectively.
For Theorems 7 and 8 retain the stated `q`/`B` dependence, all coordinate
fourth-moment constraints, and the full/symmetric-class supremum
conclusions. Finally prove that duplicating a coordinate preserves the
full rectangle distance while giving correlation gap zero.

## Certification gates

Every proposed module must be imported by the intended terminal module and
covered by the package build. Save exact commands, exit codes, versions,
dependency revisions, expanded endpoint types, and transitive axiom lists.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. A successful
build alone does not establish the axiom condition or source correspondence.

The new verification record must identify the actual proof commit and
manuscript hash, keep provisional helpers separate from certified endpoints,
and retain statement status separately from current-proof-route status.
Cache or network failures are infrastructure evidence, rather than analytic
counterexamples. Preserve the working checkpoint and historical records while
continuing independent obligations.

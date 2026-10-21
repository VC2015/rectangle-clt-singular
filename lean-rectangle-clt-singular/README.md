# Unrestricted-covariance rectangle CLTs in Lean

The three bounded-observation CLTs in the supplied companion manuscript
are proved in
[`SharpMain.lean`](RectangleCLTCompanion/SharpMain.lean): the unrestricted
covariance bound, the gap-sensitive bound, and the sharper bound under
full aggregate third-moment cancellation. The final theorems have no
unproved analytic estimate as a premise.

The bounded-observation verification report is available as a
[PDF](report/companion_verification.pdf) and
[LaTeX source](report/companion_verification.tex). Build and axiom-audit
results, exact counts, and source hashes are recorded in
[`VERIFICATION.json`](VERIFICATION.json).

The two sub-exponential upper bounds are proved in
[`SubexponentialMain.lean`](RectangleCLTCompanion/SubexponentialMain.lean)
and were first certified on **21 October 2026**. The exact checked proof
revision is [`d0131c0f3399`](https://github.com/VC2015/HDCLTs/commit/d0131c0f3399ed116ccae144e56a0d8edee9d62d).
The complete package build and strict transitive axiom audit passed;
all **258** new theorem declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Exact contracts, source hashes,
commands, and logs are recorded in
[`SUBEXPONENTIAL_VERIFICATION.json`](SUBEXPONENTIAL_VERIFICATION.json).
The original bounded verification record and report remain unchanged.

This is a separate Lake package. Keep these sibling folders together:

```text
lean-kane/                       Kane sensitivity bounds
lean-rectangle-clt-local/              Earlier local-covariance CLT
lean-rectangle-clt-singular/      Unrestricted-covariance companion
```

The earlier [local-covariance theorem](../lean-rectangle-clt-local/RectangleCLT/Main.lean)
is a separate result. The companion permits singular covariance without
its positive local four-coordinate eigenvalue hypothesis.

## The proved bounds

Let `W = sum ξᵢ`, where the vector observations are independent, centered,
and satisfy `‖ξᵢ‖∞ ≤ δ` almost surely. Their laws need not be identical,
and coordinates within one observation may be dependent. Assume `p,n ≥ 1`
and that the actual covariance `Σ = Cov(W)` has unit diagonal. The
comparison law is the concrete Gaussian pushforward `gaussianLaw A`,
where `A * A.transpose = Σ`. Such a factor exists for every admissible
array, including singular covariance; see
[`FactorExistence.lean`](RectangleCLTCompanion/FactorExistence.lean).

Put `L = log(ep)` and define

$$
D_L=1+\log_+\frac1{\delta\sqrt L},\qquad
c=1-\max_{j\ne k}|\Sigma_{jk}|,\qquad
\kappa=\begin{cases}\min\{L,1/c\},&c>0,\\L,&c=0,\end{cases}
\qquad E_\kappa=1+\log_+\frac{\sqrt\kappa}{\delta L},
$$

where `log₊ x = max(0, log x)`. For `p=1`, the empty off-diagonal
maximum is zero, so `c=1`.

For every measurable coordinate rectangle `R`, write
`Δ_R = |P(W ∈ R) − gaussianLaw A(R)|`. A single universal constant `C ≥ 1`
works in all three bounds:

| Result | Bound for `Δ_R` | Additional hypothesis |
| --- | --- | --- |
| Unrestricted covariance | `C min(1, δ L^(3/2) sqrt D_L)` | None |
| Gap-sensitive | `C min(1, δ [L^(3/2) + L sqrt(κ Eκ)])` | None; `c=0` is allowed |
| Full tensor cancellation | `C min(1, δ L sqrt(κ Eκ))` | `sum_i E[ξᵢⱼ ξᵢₖ ξᵢₗ] = 0` for every `j,k,l` |

These are uniform bounds over all `Rect p`, including open, closed,
mixed, unbounded, and empty coordinate intervals. Atomic observations
are allowed. No covariance rank, positive eigenvalue, or positive pair
gap is required. Cancellation between different observations is allowed;
vanishing marginal third moments alone is insufficient.

The public theorem
`RectangleCLT.Companion.companionCLTExists_common` states the common-constant
result. The individual APIs are `unrestrictedCLT`, `gapSensitiveCLT`,
`zeroSkewCLT`, and their `Exists` theorems. If
`K = companionUniversalConstant`, the gap-sensitive and cancellation
theorems use `K`, the unrestricted theorem uses `2K`, and `2K` works for
all three. These constants are explicit Lean definitions, independent of
the probability model and dimensions; they are not numerically optimized.

## Sub-exponential observations

Let `X₁,…,Xₙ` be independent centered vectors and set
`Wₙ = n^(-1/2) sum Xᵢ`. Their laws need not be identical, and coordinates
within one observation may be dependent. The manuscript's hypotheses are
`n,p ≥ 1`, `‖Xᵢⱼ‖ψ₁ ≤ K` with `K ≥ 1`, and
`n⁻¹ sum_i E[Xᵢⱼ²] = 1` for every coordinate. The comparison Gaussian has
the exact covariance of `Wₙ`, including when it is singular. Write

$$
b=\frac{K\log(en)}{\sqrt n},\qquad L=\log(ep),\qquad
D=1+\log_+\frac1{b\sqrt L},\qquad
F=1+\log_+\frac1{bL}.
$$

The two end-to-end targets, uniformly over all `Rect p`, are

$$
\Delta_R\le C\min\{1,bL^{3/2}\sqrt D\}
$$

and, if the correlation gap of `Cov(Wₙ)` is at least a fixed `c₀ > 0`,

$$
\Delta_R\le C_{c_0}\min\{1,
b[L^{3/2}+L\sqrt F]\}.
$$

Here `C` is universal, and `C_c₀` depends only on `c₀`. Neither constant
depends on `n`, `p`, `K`, the observation laws, or a covariance eigenvalue.
There is no positive-gap requirement for the first bound.

All theorem names in the following table are in `RectangleCLT.Companion`.
The exact contracts are defined in
[`SubexponentialStatement.lean`](RectangleCLTCompanion/SubexponentialStatement.lean)
and [`SubexponentialOrlicz.lean`](RectangleCLTCompanion/SubexponentialOrlicz.lean).

| API in `SubexponentialMain.lean` | Observation contract | Constant |
| --- | --- | --- |
| `subexponentialCLT` | Coordinate exponential moments at scale `K`; actual covariance has unit diagonal | `subexponentialUniversalConstant` |
| `fixedGapSubexponentialCLT hc₀` | Same, with correlation gap at least `c₀ > 0` | `subexponentialGapConstant c₀` |
| `subexponentialCLT_psi1` | The infimum-based `ψ₁` bound at `K` and averaged coordinate second moments equal to one | `2 * subexponentialUniversalConstant` |
| `fixedGapSubexponentialCLT_psi1 hc₀` | Same Orlicz contract and a fixed positive correlation gap | `2 * subexponentialGapConstant c₀` |

The exponential-moment contract explicitly includes integrability of
`exp(|Xᵢⱼ|/K)` and its expectation bound by two. This prevents a
nonintegrable function's totalized Bochner integral from satisfying the
contract spuriously. The Orlicz norm is the infimum of genuine admissible
positive scales, with value `∞` when none exists. Its bound at `K` supplies
an admissible scale below `2K`; monotonicity then gives exponential moments
at `2K`. This avoids assuming attainment of the infimum. The rate lemmas
absorb the scale change with a further universal factor two, as recorded
in the table.

`subexponentialCLTExists` and `fixedGapSubexponentialCLTExists` choose their
constants before the probability space, dimensions, distributions, and
tail scale. `gaussian_factor_exists_of_subexponential` constructs an actual
Gaussian covariance factor for every admissible array. The target factor
quantifier therefore permits singular covariance without being vacuous.

## Sub-exponential proof path

The extension clips each coordinate at `T = K u`, where `u = 4 log(en)`.
Its residual coupling uses a direct exponential-moment estimate. For one
coordinate, let `R = X − clip_T(X)`. The pointwise inequality

$$
e^{|R|/K}\le 1+e^{-u}e^{|X|/K}
$$

gives `E exp(|R|/K) ≤ 1 + 2 exp(−u)`. Independence between observations
bounds the exponential moment of their sum of absolute residuals by
`exp(2n exp(−u))`. The centering cost is at most `2nK exp(−u)`. Markov's
inequality and a coordinate union bound therefore yield

$$
\Pr\!\left\{\left\|n^{-1/2}\sum_i(R_i-ER_i)\right\|_\infty
>\frac{K[s+4ne^{-u}]}{\sqrt n}\right\}
\le pe^{-s}.
$$

Taking `s = log(4np)` controls the discarded sum while keeping the clipping
threshold dependent on `log n` alone. The implementation does not require
the event that all `np` original coordinates lie below the clipping level.

| Module | Role in the extension |
| --- | --- |
| [Clipping](RectangleCLTCompanion/SubexponentialClipping.lean), [ResidualMGF](RectangleCLTCompanion/SubexponentialResidualMGF.lean), and [Bernstein](RectangleCLTCompanion/SubexponentialBernstein.lean) | Actual clipped residual moments, the direct product exponential-moment estimate, and the normalized residual coupling. The file named `Bernstein` implements this direct tail argument. |
| [Array](RectangleCLTCompanion/SubexponentialArray.lean) and [L2](RectangleCLTCompanion/SubexponentialL2.lean) | Measurability, row independence, centering, second moments, exact sum decomposition, and clipped marginal standard deviations. |
| [Scaling](RectangleCLTCompanion/SubexponentialScaling.lean) and [Bounded](RectangleCLTCompanion/SubexponentialBounded.lean) | Positive diagonal standardization, interval pullbacks for every endpoint convention, exact Gaussian factor scaling, and application of the bounded CLTs. |
| [Gaussian](RectangleCLTCompanion/SubexponentialGaussian.lean) | Joint Gaussian realization of the covariance of the clipped and residual sums, including both cross blocks, and Gaussian residual tails. |
| [Transfer](RectangleCLTCompanion/SubexponentialTransfer.lean) and [Reduction](RectangleCLTCompanion/SubexponentialReduction.lean) | Two coupling sandwiches, the proved Gaussian rectangle concentration bound, and transfer to all rectangles. The components within either coupling may be dependent. |
| [PairGap](RectangleCLTCompanion/SubexponentialPairGap.lean) and [Gap](RectangleCLTCompanion/SubexponentialGap.lean) | Correlation-gap stability from entrywise covariance perturbations and the actual coordinate `L²` errors. |
| [Rates](RectangleCLTCompanion/SubexponentialRates.lean), [Scales](RectangleCLTCompanion/SubexponentialScales.lean), and [Orlicz](RectangleCLTCompanion/SubexponentialOrlicz.lean) | Dimension and sample-size logarithms, absorption of the coupling errors, and the exact Orlicz-norm bridge. |

Covariance restoration uses a jointly Gaussian pair `(Z_T,H)` with the
block covariance of the actual clipped and residual sums. Thus `Z_T + H`
has exactly the original covariance. The cross blocks are retained;
independence of `Z_T` and `H` is not assumed. The existing
[clipping counterexample](RectangleCLTCompanion/CovarianceRestoration.lean)
shows why independent added noise cannot generally restore the covariance.

## Proof and checked components

The proof uses the actual Bernoulli-retained-array and Gaussian
interpolation laws. It preserves the signed aggregate third tensor
before estimating the cubic term. Its Gaussian surface step is a direct
smooth integration-by-parts and tube argument. A general Hausdorff
surface measure and full first-variation theorem for polyhedra are not
asserted by this development.

| Component | Checked role in the final proof |
| --- | --- |
| [Concentration](RectangleCLTCompanion/Concentration.lean) and [GaussianConcentration](RectangleCLTCompanion/GaussianConcentration.lean) | Actual rectangle boundary concentration, with arbitrary independent measurable shifts. Constants are `2^30` for bounded sums and `12 exp(3/2)` for Gaussians; singular covariance is allowed. The bounded input uses the proved Kane sensitivity chain. |
| [Prékopa](RectangleCLTCompanion/Prekopa/PrekopaLeindler.lean) and [TiltContraction](RectangleCLTCompanion/TiltContraction.lean) | Finite-dimensional Prékopa–Leindler and covariance contraction for the actual Gaussian selector tilt, including rectangular singular factors. |
| [SelectorMeanBound](RectangleCLTCompanion/SelectorMeanBound.lean) and [SelectorMatrixBound](RectangleCLTCompanion/SelectorMatrixBound.lean) | Actual Gaussian entropy, averaged selector means, and the matrix reduction used by restoration. |
| [SupportRows](RectangleCLTCompanion/SupportRows.lean) and [SharpRepresentatives](RectangleCLTCompanion/SharpRepresentatives.lean) | Singular support coordinates and bounded representatives preserving the original laws and observable envelope. The support covariance is a projection at most identity; no inverse-eigenvalue loss enters the estimates. |
| [FourthIdentityPath](RectangleCLTCompanion/FourthIdentityPath.lean) and [FourthIdentitySelectorFubini](RectangleCLTCompanion/FourthIdentitySelectorFubini.lean) | Exact signed fourth-order interpolation identities, genuine fresh-copy product laws, and justified integral exchanges. |
| [SignedSurfaceClosure](RectangleCLTCompanion/SignedSurfaceClosure.lean) | Actual Gamma-clock facet/ridge tube bounds, disjoint image probabilities, Gaussian dyadic moments, and the completed averaged signed power-trace estimate. |
| [SharpTraceApplication](RectangleCLTCompanion/SharpTraceApplication.lean) and [RestorationFourthBound](RectangleCLTCompanion/RestorationFourthBound.lean) | The trace and matrix estimates on the full retained-array/split-Gaussian law, then common-base restoration. No maskwise concentration assumption is used. |
| [SharpMainAssembly](RectangleCLTCompanion/SharpMainAssembly.lean), [SharpEndpoint](RectangleCLTCompanion/SharpEndpoint.lean), and [Optimization](RectangleCLTCompanion/Optimization.lean) | Actual early/late path estimates, time integration, sharp endpoint smoothing, transfer to every rectangle, and bandwidth optimization. |
| [SharpMain](RectangleCLTCompanion/SharpMain.lean) | Discharges the intermediate matrix-family and variational propositions and proves the three bounded CLTs. |

The generic surface estimate retains its true dependence on the input
concentration constant `C₀`. In the checked code,

$$
C_{\rm surface}(C_0)
=160e^{3/2}C_0\bigl(8e^{80}+16e^{136}\bigr).
$$

The actual split-law application supplies the fixed absolute constant
`C₀ = 2^30 + 12 exp(3/2)`. Thus the final theorem's constant is universal.
The intermediate conditional reductions remain useful APIs; their
analytic premises are proved and supplied by `SharpMain.lean`.

Prékopa–Leindler adapts Jonathan Ho's
[`isoperimetric`](https://github.com/hojonathanho/isoperimetric)
formalization at commit
`29768f8beeaf17295cdf3853d37da35d7e2b0a5f`, under **Apache License 2.0**.
The license, upstream toolchain/revision, and compatibility changes are
recorded in [the attribution file](third_party/isoperimetric/README.md).
No Prékopa or covariance-contraction axiom was added.

## Remaining scope

The sub-exponential APIs do not assert a zero-skewness improvement.
Clipping need not preserve cancellation of aggregate third tensors across
different rows, and the transfer bound includes a `b L^(3/2)` contribution.
The bounded full-tensor cancellation theorem remains as stated above.
The supplement's lower bounds and consistency thresholds are outside the
formalized scope.

The checked [finite model](RectangleCLTCompanion/Models.lean) with
covariance

$$
\Sigma=\begin{pmatrix}1&0&3/5\\0&1&4/5\\3/5&4/5&1\end{pmatrix}
$$

has pair gap `1/5` but local parameters `a3=a4=0`. It is realized by
`(X,Y,(3X+4Y)/5)` for independent symmetric signs. This demonstrates
scope beyond the earlier local theorem. A separate finite probability
example `(X,Y,XY)` has all marginal third moments zero but a mixed third
moment equal to one, distinguishing the full cancellation hypothesis.

## Reproduce the verification

The package pins **Lean 4.19.0** and **mathlib v4.19.0**. Keep the sibling
packages above, then run from `lean-rectangle-clt-singular/`:

```sh
lake build
lake env lean RectangleCLTCompanion/Audit.lean
lake env lean RectangleCLTCompanion/MainAudit.lean
lake env lean RectangleCLTCompanion/CompleteAudit.lean
(cd ../lean-rectangle-clt-local && lake env lean RectangleCLT/Audit.lean)
```

For the staged sub-exponential extension, build and inspect the actual
end-to-end theorem types and their dependency closure:

```sh
lake build RectangleCLTCompanion.SubexponentialMain RectangleCLTCompanion.SubexponentialAudit
lake env lean RectangleCLTCompanion/SubexponentialAudit.lean
```

`SubexponentialAudit.lean` prints both observation contracts, checks the
four end-to-end CLT APIs and factor existence, and rejects every
nonstandard axiom in the transitive closure of the new sub-exponential
theorem declarations. Its final successful output, source hashes, exact
counts, proof commit, and verification date belong in the separate
`SUBEXPONENTIAL_VERIFICATION.json` record. A successful intermediate module
build does not replace this end-to-end check.

The audits display theorem types and check transitive axiom dependencies.
The permitted dependencies are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. See
[`VERIFICATION.json`](VERIFICATION.json) for the saved build/audit results,
counts, and hashes; the report does not substitute guessed counts for
that record.

## Research sources

The user's **20 October 2026** split package is preserved byte for byte:

- Main manuscript: [LaTeX](sources/Rectangle_CLT_Main.tex) and
  [PDF](sources/Rectangle_CLT_Main.pdf).
- Supplement: [LaTeX](sources/Rectangle_CLT_Supplement.tex) and
  [PDF](sources/Rectangle_CLT_Supplement.pdf).
- [Byte counts and SHA-256 hashes](sources/MANIFEST.json).

The original documents retain their credits and research claims. This is
the preserved historical source snapshot; the current research manuscript
is in [the sibling paper folder](../research-rectangle-clt-singular/).
Its supplementary lower bounds and consistency thresholds remain beyond
the certification scope described above.

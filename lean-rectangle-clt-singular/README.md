# Unrestricted-covariance rectangle CLTs in Lean

The three bounded-observation CLTs in the supplied companion manuscript
are proved in
[`SharpMain.lean`](RectangleCLTCompanion/SharpMain.lean): the unrestricted
covariance bound, the gap-sensitive bound, and the sharper bound under
full aggregate third-moment cancellation. The final theorems have no
unproved analytic estimate as a premise.

The verification report is available as a
[PDF](report/companion_verification.pdf) and
[LaTeX source](report/companion_verification.tex). Build and axiom-audit
results, exact counts, and source hashes are recorded in
[`VERIFICATION.json`](VERIFICATION.json).

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

## Scope beyond the three bounded theorems

The normalized-observation and positive diagonal-scaling corollaries do
not yet have separate companion theorem APIs. The complete sub-exponential
clipping and probabilistic coupling argument, and the supplement's lower
bounds and consistency thresholds, are not formalized here.

Some supporting facts are proved independently:
[joint covariance restoration](RectangleCLTCompanion/CovarianceRestoration.lean)
retains both covariance cross blocks, and a clipping counterexample shows
that the difference between original and clipped covariance need not be
positive semidefinite. This algebra alone does not establish the
sub-exponential extension.

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

The original documents retain their credits and research claims. Their
scope is broader than the three bounded CLTs formalized here.

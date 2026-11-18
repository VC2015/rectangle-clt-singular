# Actual positive ordered-pair means

Import `RectangleCLTArxivV1.PositiveGammaMeans`.

The checked final endpoints are:

- `positiveGammaSoftOrderedPairMass_concentrated_base`
- `positiveGammaSoftOrderedPairProjection_concentrated_base`

Both take `hp ν U f a hK hδ hσ hh hu hbase hδσ`. Here `hbase` is the original uniform full-family layer concentration bound `K*(s+δ)`, `hδσ` is `δ*sqrt(dimensionLog p)≤σ`, and both the smoothing width `h` and Gaussian scale `σ` are positive. The base law is any probability law, including a singular law.

The actual baseline functions are defined in `PositiveGammaPairSum`:

- `positiveGammaSoftOrderedPairMass u a h σ x` is the Gaussian expectation of the complete ordered-pair sum `lambda_jl * F(x+σG) * pi_j(x+σG) * pi_l(x+σG)`.
- `positiveGammaSoftOrderedPairProjection` includes the additional actual squared norm `||supplementalHPairPlane(u_j,u_l) G||²`.

The original angle weight is retained. Parallel and diagonal contributions are proved zero. No pair gap or full-family independence is required.

The endpoints include genuine base integrability. Their means are bounded respectively by

`positiveSoftPairMassConstant * h² * K * sqrt(L) / σ`

and

`positiveSoftPairProjectionConstant * h² * K * (L*sqrt(L)) / σ`,

where the two fixed positive numerical constants are `1024*pi*exp(3/2)*exp(128)` and `4096*pi*exp(3/2)*exp(128)`.

The exact pointwise Gamma identities have coefficient `h²/(2*σ²)` against the *ordered* hard positive-edge sum. This equals the printed `h²/σ²` coefficient against the *unordered* ridge sum. The bare-mass budget uses the sharp R2 tube estimate; the projected-moment budget uses R4. Both constants are fixed before all model data.

`checkpoint-1/run.json` records the actual selected build, forced source elaboration, strict six-public-declaration audit, expanded endpoint types and kernel-derived project dependency graph. The private Gamma/base integrability and Fubini transfer is in the same source and is included transitively in the checked headline dependency graph. The exact source passages and the companion 17-target ordered-sum receipt are recorded in `correspondence/supplemental-h-positive-means-passages.json`.

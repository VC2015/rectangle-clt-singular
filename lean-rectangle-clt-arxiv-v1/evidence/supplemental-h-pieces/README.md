# Supporting Supplemental H proofs

These proofs concern the frozen supplement at
`1803366cc994d9facae8e128ee180f68e319486f` (SHA-256
`5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb`).
They are supporting pieces, not a certification of the named surface,
cubic, pair, or fourth-derivative results.

`SupplementalHProjectedMean.lean` proves the projected-reference mean
inequality of lines 1319–1375 for actual bounded weights and any symmetric
idempotent matrix projection. It supplies the actual Gaussian tilt identity,
weighted Jensen, orthogonal mean decomposition, and weighted
Cauchy–Schwarz. The tilt identity uses the exact Cameron–Martin formula;
the manuscript motivates that identity by Gaussian orthogonal independence.
This difference must be retained in a proof-route review. The nuclear
reduction for bounded nonnegative log-concave weights reuses the checked
Prékopa argument. Its affine logistic-selector specialization has no
covariance-contraction or nuclear-estimate hypothesis.

The extension of covariance contraction to all weights with linear growth
in the statement at lines 1304–1325 is not supplied here.

`SupplementalHLocalizedTube.lean` proves the actual outward tube estimate
in the conditioning step at lines 1196–1208, applied to the localization
target defined at lines 1025–1030:

`E[R(G)^4 1_tube] ≤ K (σ E[R(G)^3] + δ E[R(G)^4])`.

The base has the displayed concentration hypothesis of lines 909–913;
the Gaussian is independent under the actual product law. Threshold
translation, measurability, weighted integrability and Fubini are proved.
The moment assumptions are ordinary integrability assumptions on the
displayed random radius, with actual Gaussian integrals on the right.

The actual projection radius and its quantitative moments are now supplied
in `SupplementalHRadius.lean`; the combined check is recorded separately in
`../supplemental-h-radius-scaling/`. The comparison of the actual Hausdorff
surface quantities to that tube remains open. No desired surface estimate
occurs as an input to these proofs.

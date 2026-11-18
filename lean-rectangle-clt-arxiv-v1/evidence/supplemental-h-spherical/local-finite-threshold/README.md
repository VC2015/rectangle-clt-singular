This checkpoint proves local genuine derivatives of the actual finite
Gaussian threshold CDF with arbitrary nonunit and zero normals.
`LocalFiniteThresholdRegularity` is ordinary geometric slack data: each
retained zero normal has nonzero threshold, and each remaining parallel
inequality in a selected normalized normal section has nonzero affine
slack. The set of such threshold vectors is proved open. No desired
derivative, boundary identity, or smooth extension is a premise.

The nonzero selected normal is explicitly normalized with standard
deviation `sigma=sqrt(vectorNormSq u_j)`, retaining the exact `1/sigma`
Jacobian. A selected zero inequality gives a constant-in-threshold
probability on either side of zero. Coordinates outside the finite face
set have derivative zero. The local partials theorem then gives the
actual Frechet gradient of genuine finite coordinate derivatives.

Two actual Gaussian integral identities follow from this gradient and
independently proved Gaussian log-dilation/translation differentiation:
the radial score is `-sum_j b_j*finiteFirst_j`, and the first moment in
direction `v` is `-sum_j dot(u_j,v)*finiteFirst_j`. Both identities also
have retained-face sum versions. All integrals use the actual finite
hard-event indicator. These are supporting differential identities, not
the final quantitative H.1 localization bounds.

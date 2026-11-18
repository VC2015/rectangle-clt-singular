# Supplemental H radius and finite-bound weight reductions

These are supporting proofs for the frozen supplement. They do not assert
the localized Hausdorff facet/ridge surface theorem.

`SupplementalHRadius.lean` constructs one plus the largest projection norm
onto every three-tuple of signed face directions. Padding proves control of
all spans of at most three normals; dependent and empty tuples are included.
The actual finite Gaussian construction supplies every natural moment and
exponential-polynomial moments. Its moment proof reuses the archived
finite-subspace Gaussian maximum estimate, rather than the printed
chi-square-tail calculation; this is an explicit alternative analytic route
to the same dimension-logarithm powers.

The radius discharges all moment premises in the actual independent
Gaussian outward-tube estimate, giving
`C K (σ L sqrt(L) + δ L²)`. Under `δ sqrt(L) ≤ σ`, the bound becomes
`2 C K σ L sqrt(L)`. The base concentration assumption is precisely the
displayed concentrated-base hypothesis; no surface estimate is assumed.

`SupplementalHWeightScaling.lean` removes the artificial upper bound one
from the Gaussian projected-reference and nuclear reductions. Any finite
positive bound works, and its normalization cancels from masses, means,
scores and the entropy ratio. This allows bounds depending on the fixed
base point, without introducing that bound into the conclusion. The
extension to genuinely unbounded linear-growth weights is a separate
obligation.

`run.json` records the combined build, forced source elaborations and
strict transitive axiom audit. The allowlist is `propext`,
`Classical.choice`, and `Quot.sound`.

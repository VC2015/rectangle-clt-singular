This checkpoint completes only the optional duplication paragraph at frozen
main TeX lines 8489–8497, PDF page 103. It does not alter a lower-bound
headline or the historical lower ledger.

`duplicateCoordinates` is the actual surjective coordinate reindexing.
Its existing norm identity gives the same pointwise envelope. Composition
with this measurable map preserves independence and identical laws; its
linearity under negation preserves central symmetry. Arbitrary scalar
coordinate integral functionals are definitionally reindexed, and arbitrary
norm integral functionals are exactly unchanged. This covers every stated
coordinate moment and polynomial/Orlicz norm envelope.

`exists_duplicateCoordinates_comparison` applies `gaussian_factor_exists`
to the proved duplicated bounded-independent hypotheses and thereby
constructs the new square factor internally. Actual covariance reindexing
identifies its Gaussian law with the duplicated original Gaussian law.
The existing full measurable rectangle preimage/lift argument gives exact
rectangle distance, and integrating the pointwise norm equality gives exact
Gaussian maximum mean.

`exists_coordinatePadding_zero_gap_comparison` specializes to `p+1`
coordinates, retaining every original coordinate and copying coordinate
zero. Unit marginal variance remains one. The repeated pair gives actual
pair gap zero through the unit-Gram bound on all covariance entries.

The two final scalar theorems prove
`dimensionLog(p+1)/dimensionLog(p) → 1` and its composition with any
dimension sequence tending to infinity. Eventually the logarithm is
`1+log p`; the adjacent-log increment tends to zero while the denominator
tends to infinity. The spherical-balance child independently developed this
scalar leaf in scratch space, and it was then compiled within the final
module.

All twelve public declarations have a fresh build, forced source
elaboration, full type/dependency export and strict audit allowing only
`propext`, `Classical.choice`, and `Quot.sound`.

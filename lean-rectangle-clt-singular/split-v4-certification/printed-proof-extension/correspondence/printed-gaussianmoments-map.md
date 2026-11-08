# Gaussian maximum printed moment route

Finite-dimensional probability spaces vary with m. Normalized maxima are indexed by m=n+2 to omit irrelevant m=0,1; the proved uniform-integrability condition is the identical law expectation-tail criterion on each actual space. The mean limit is extended back to m→∞. Integrability is established directly from finite coordinate second moments before the Gaussian union tail is integrated. Probability barriers now use the exact printed quantile; the prior CDF=e^-1 quantile and all previous records are retained.

| TeX | Printed step | Earlier proof | Added exact declarations |
|---|---|---|---|
| 4114 | literal Mills quantile m*tail(u_m)=1 | ALTERNATIVE_BYPASS | `RectangleCLT.Companion.SplitV4.Printed.printedNormalMaxThreshold_tail_identity`, `RectangleCLT.Companion.SplitV4.Printed.standardNormalCDF_printedNormalMaxThreshold` |
| 4117 | threshold scale and density at the literal printed quantile | ALTERNATIVE_BYPASS | `RectangleCLT.Companion.SplitV4.Printed.tendsto_printedNormalMaxThreshold_div_sqrt_two_log`, `RectangleCLT.Companion.SplitV4.Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log` |
| 4131 | normalized maximum converges in probability via Mills/CDF powers | UNVERIFIED_STEP | `RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_in_probability` |
| 4132 | actual union tail integrated for logarithmic second moment | ALTERNATIVE_BYPASS | `RectangleCLT.Companion.SplitV4.Printed.gaussian_norm_tail_union`, `RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_by_union_tail`, `RectangleCLT.Companion.SplitV4.Printed.integral_gaussian_norm_sq_le_four_dimensionLog` |
| 4133 | L2 boundedness gives uniform expectation tails | UNVERIFIED_STEP | `RectangleCLT.Companion.SplitV4.Printed.integral_normalizedGaussianMaximum_sq_le`, `RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_tail`, `RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_uniform_integrability` |
| 4134 | probability convergence and uniform integrability imply L1/mean convergence | ALTERNATIVE_BYPASS | `RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_L1_error_bound`, `RectangleCLT.Companion.SplitV4.Printed.normalizedGaussianMaximum_tendsto_L1`, `RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability` |

Build and strict transitive audit pass. 69 added theorem declarations; only propext/Classical.choice/Quot.sound; 44,409 constants in new mean/UI closure excluding old mean endpoint and old quantitative maximum second-moment endpoints.

No incorrect printed passage or additional hypothesis found in this scope.

# Printed global maxima comparison coverage

Frozen manuscript `2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`. The old local result proofs remain unchanged.

- **Rademacher-scalar-F1**, tex4074–4086: **SAME_ARGUMENT**. Actual centered sign increments and the independent product law now instantiate the NEW fully printed all-threshold F1 theorem, reaching literal copy variance and Laplace integration by parts even for small thresholds. Old F1/small-x/log-tail endpoints are absent from the new global closure.
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacher_log_tail_printed`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_damped_error`
- **Rademacher-low-threshold**, tex4088–4092: **SAME_ARGUMENT**. The genuine scalar Berry–Esseen estimate plus a fixed scalar CDF cap r0<1 gives the printed exponentially damped m*r0^(m-1) uniform bound for every real x≤1.
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacher_scalar_berryEsseen`
  - `RectangleCLT.Companion.SplitV4.Printed.probability_power_difference_with_cap`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_low_error`
- **Rademacher-damped-power**, tex4093–4098: **SAME_ARGUMENT**. Tail comparability, the finite power mean-value bound and (1-z)^k≤exp(-kz) establish the actual w*exp(-c*w) factor before any uniform maximization.
  - `RectangleCLT.Companion.SplitV4.Printed.probability_power_difference_with_tail_comparison`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_damped_error`
- **Rademacher-central-moderate**, tex4099–4099: **SAME_ARGUMENT**. For x≤2sqrt(log(em)), the scalar remainder is bounded by the stated two-term rate and exponential damping removes the m dependence.
  - `RectangleCLT.Companion.SplitV4.Printed.rademacherRelativeTailError_central`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_central_error`
- **Rademacher-far-moderate**, tex4100–4101: **SAME_ARGUMENT**. For x≥2sqrt(log(em)), w≤exp(-x²/4); the polynomial remainder times this Gaussian exponential is explicitly bounded by O(n^-1/2).
  - `RectangleCLT.Companion.SplitV4.Printed.normal_tail_mass_far_positive`
  - `RectangleCLT.Companion.SplitV4.Printed.polynomial_times_gaussian_le`
  - `RectangleCLT.Companion.SplitV4.Printed.rademacherRelativeTailError_gaussian_weighted`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_moderate_far_error`
- **Rademacher-outer-cutoff**, tex4102–4105: **SAME_ARGUMENT**. The actual independent sign MGF is a cosh product and is sub-Gaussian. Both scalar tails give the printed 2*m*exp(-x²/2) outer bound and the dimension range gives O(n^-1/2).
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf_le`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherUpperTail_subgaussian`
  - `RectangleCLT.Companion.SplitV4.Printed.standardNormalUpperTail_subgaussian`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_outer_error`
  - `RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_above_cutoff_error`
- **Rademacher-global-rate-and-range**, tex4061–4071: **SAME_ARGUMENT**. Explicit absolute positive amplitude and constants discharge the moderate-tail hypotheses uniformly for all sufficiently large n. The terminal has every x and every m≥2 with log(em)≤a1*sqrt n, and exact rate sqrt(log(em))/sqrt n+log(em)²/n. No analytic estimate is a premise.
  - `RectangleCLT.Companion.SplitV4.Printed.rademacherCutoffAmplitude_bounds`
  - `RectangleCLT.Companion.SplitV4.Printed.eventually_rademacher_cutoff_conditions`
  - `RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error`
- **Gaussian-exact-density-derivative**, tex4135–4138: **SAME_ARGUMENT**. Existing genuine derivative formula is exactly the printed two-term expression.
  - `RectangleCLT.Companion.SplitV4.hasDerivAt_normalMaximumDensity`
- **Gaussian-negative-region**, tex4139–4140: **SAME_ARGUMENT**. For x≤0, a fixed positive scalar tail and exponential CDF damping uniformly bound both terms. Using the fixed tail at zero instead of substituting its value 1/2 is a routine constant adaptation; m2,3 are handled separately.
  - `RectangleCLT.Companion.SplitV4.Printed.standardNormalPDF_le_at_zero`
  - `RectangleCLT.Companion.SplitV4.Printed.abs_mul_standardNormalPDF_le_at_zero`
  - `RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_negative_region`
  - `RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_small_dimension`
- **Gaussian-central-positive-region**, tex4141–4143: **SAME_ARGUMENT**. The printed Mills bound and w+w² exponential damping are checked before restricting x≤2sqrt(log(em)).
  - `RectangleCLT.Companion.SplitV4.Printed.standardNormalPDF_le_uniform_mills`
  - `RectangleCLT.Companion.SplitV4.Printed.normalCDF_power_pred_le_exp_half_tail`
  - `RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_tail_envelope`
  - `RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_positive_region`
- **Gaussian-far-positive-region**, tex4144–4145: **SAME_ARGUMENT**. For log(m)≤x²/4, the genuine Gaussian density exponential bounds both printed terms; the three regions combine to the global sup curvature bound C*log(em).
  - `RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_far_positive`
  - `RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_global_bound`
  - `RectangleCLT.Companion.SplitV4.Printed.normalMaximumCDF_second_derivative_global_bound`

All substantive printed arguments for the global Rademacher comparison and global Gaussian curvature are covered. The exact-quantile/probability/tail-integrability/mean route is assigned separately.

Strict audits: Gaussian curvature27 and Rademacher47 theorem declarations, all transitive dependencies use only `propext`, `Classical.choice`, `Quot.sound`. No manuscript repair identified here.

The final global Rademacher closure now positively reaches the printed all-x F1, strict Laplace IBP and independent-copy variance intermediates (54,475 constants); it excludes old F1, its small-x branch and old log-tail/pointwise endpoints.

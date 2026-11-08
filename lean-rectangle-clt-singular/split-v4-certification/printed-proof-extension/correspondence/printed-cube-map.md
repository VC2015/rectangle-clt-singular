# Printed C.1 and bounded Lemma 1 coverage

Frozen manuscript: `2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`; SHA256 `f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`.

All substantive arguments in this assigned scope are covered. The earlier result proof and evidence remain unchanged.

- **C1-edge-support** ([3164, 3181]): **SAME_ARGUMENT**. The printed convex antiderivative and its composition now exist as actual real functions; local strict uniqueness identifies genuine Fréchet derivatives at all vertices. Existing supporting-edge lemmas give the same printed edge inequalities.
  - `RectangleCLT.Companion.SplitV4.Printed.convexOn_realAffineCubeMaximum`
  - `RectangleCLT.Companion.SplitV4.Printed.convexOn_cubeRampPrimitive_comp_maximum`
  - `RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_maximum`
  - `RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.hasFDerivAt_ramp_composition`
- **C1-edge-window-squares** ([3182, 3192]): **SAME_ARGUMENT**. Exact manuscript constants H=h+8b and c=t−6b; slope-squared control at both edge ends.
- **C1-discrete-IBP-and-bound** ([3192, 3203]): **SAME_ARGUMENT**. The exact actual-gradient discrete IBP and both displayed gradient bounds are proved; the unique-case result is derived from those bounds, not from the old final C1 bound.
  - `RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.gradient_energy_eq`
  - `RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_eq_flux`
  - `RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_lower`
  - `RectangleCLT.Companion.SplitV4.Printed.CubeUniqueMax.avg_gradient_radial_upper`
  - `RectangleCLT.Companion.SplitV4.Printed.cube_boundary_unique_case`
- **C1-generic-small-threshold-perturbation** ([3204, 3205]): **SAME_ARGUMENT**. A scalar threshold perturbation avoids the finitely many forbidden pair-equality slopes at all cube vertices, with strict error < rho in each threshold.
  - `RectangleCLT.Companion.SplitV4.Printed.exists_small_threshold_perturbation`
  - `RectangleCLT.Companion.SplitV4.Printed.exists_small_unique_threshold_perturbation`
- **C1-original-event-in-expanded-perturbed-event** ([3205, 3206]): **SAME_ARGUMENT**. Uniform stability proves the exact closed-event inclusion in [t-rho,t+h+rho]; no atomlessness or indicator continuity is used.
  - `RectangleCLT.Companion.SplitV4.Printed.affineCubeMaximum_threshold_stability`
  - `RectangleCLT.Companion.SplitV4.Printed.cube_boundary_event_subset_perturbed`
  - `RectangleCLT.Companion.SplitV4.Printed.cube_boundary_indicator_le_perturbed`
- **C1-rho-limit** ([3207, 3207]): **SAME_ARGUMENT**. The numerical bounds for every positive rho pass to rho=0 along 1/(k+1); the event remains the original closed event throughout.
  - `RectangleCLT.Companion.SplitV4.Printed.cube_boundary_bound_of_all_positive_radii`
  - `RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed_avg`
  - `RectangleCLT.Companion.SplitV4.Printed.intrinsic_cube_boundary_printed`
- **C1-logarithmic-MGF** ([3209, 3215]): **SAME_ARGUMENT**. Actual cosh product, cosh≤exp(square/2), log-sum-exp and optimized logarithmic bound follow the printed method.
- **L1-paired-copy-sign-representation** ([3219, 3236]): **SAME_ARGUMENT**. Actual joint product laws, independent signs and conditional row-square expectation are proved.
- **L1-intrinsic-conditional-maximum** ([3238, 3249]): **SAME_ARGUMENT**. Sign invariance of independent paired differences, Fubini, triangle inequality preserve the intrinsic maximum.
- **L1-conditional-bound** ([3250, 3259]): **SAME_ARGUMENT**. The conditional good-variance estimate is re-proved through the new printed C1 endpoint, then combined with actual copy-selection law, contraction, variance Markov and Fubini arguments.
  - `RectangleCLT.Companion.SplitV4.Printed.cube_translated_boundary_printed`
  - `RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed`
- **L1-square-contraction** ([3262, 3288]): **SAME_ARGUMENT**. Same one-sign maxima pairing, iteration, zero-extended family and reflection argument with exact factor4eta.
- **L1-symmetrization-bad-variance** ([3290, 3313]): **SAME_ARGUMENT**. Same conditional Jensen/copy symmetrization, sign invariance, contraction and Markov with intrinsic8eta/32eta budgets.
- **L1-average-intrinsic** ([3314, 3322]): **SAME_ARGUMENT**. The complete intrinsic (8s+64eta)/v bound is re-proved with the printed C1 route supplied conditionally; the existing subsequent logarithmic/variance/independent-shift arguments remain the same printed route.
  - `RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed`
- **L1-log-consequence** ([3324, 3340]): **SAME_ARGUMENT**. Same scalar exponential Taylor bound, independence, exponential maximum and small/large envelope split; explicit constants and variance normalization are routine adaptations.
- **L1-face-and-independent-shift** ([None, None]): **SAME_ARGUMENT**. Standardized face map, rescaling to general v and arbitrary independent shift use genuine law transport; the Gaussian half is assigned separately.

The original tie-safe intrinsic_cube_boundary_avg remains unchanged. New intrinsic_cube_boundary_printed instead follows unique-maximizer gradients, generic perturbation, closed-event enlargement and numerical radius limit; no old final C1 bound is used.

Strict audit: all 41 new theorem declarations, including complete dependency closures, use only `propext`, `Classical.choice`, `Quot.sound`. Build and fresh audit logs: `/tmp/printed-cube-audit-build.log`, `/tmp/printed-cube-audit.log`. No manuscript repair found in this scope.

The bounded final logarithmic consequence is already the printed scalar-MGF/independence/small-versus-large-envelope route. The new file re-verifies its substantive intrinsic input through the printed C1 route; the existing general-variance/face/independent-shift transport is a routine adaptation.

# Printed endpoint-route map

The baseline result certificate is preserved. All printed endpoint steps have new SAME_ARGUMENT evidence. `Printed` abbreviates `RectangleCLT.Companion.SplitV4.Printed`.

| Step | TeX lines / label | Printed claim | Baseline | New checked route |
|---|---|---|---|---|
| A-mixture | 1797–1808; appx-sec:mixture; eq:mixture | F is actual exponential random-rectangle probability; Fubini gives its expectation | SAME_ARGUMENT | RectangleCLT.FaceSmoother.F_eq_exponential_probability; RectangleCLT.FaceSmoother.integral_F_eq_randomRectangle_average |
| A-radius | 1754–1754; appx-sec:smoothing; Lemma2 proof | R_h=h max over signed faces |log(omega_f/omega_0)| with genuine measurability/integrability | UNVERIFIED_STEP | Printed.clockLogVector; Printed.clockLogMaximum; Printed.randomThresholdRadius; Printed.integrable_randomThresholdRadius; Printed.randomThresholdShift_norm |
| A-single-tail | 1758–1762; appx-sec:smoothing; Lemma2 proof | P(|log(omega_f/omega_0)|>s)=2/(1+exp s)<=2exp(-s) | UNVERIFIED_STEP | Printed.clock_abs_log_ratio_tail; Printed.clock_abs_log_ratio_tail_le |
| A-union-tail | 1764–1765; appx-sec:smoothing; Lemma2 proof | P(R_h>h s)<=min(1,2m exp(-s)), m=2p | UNVERIFIED_STEP | Printed.clockLogMaximum_tail_le; Printed.randomThresholdRadius_tail_le_min |
| A-layercake | 1765–1767; appx-sec:smoothing; Lemma2 proof | Integrate tail: E R_h<=h(log(2m)+1)<=C h L | UNVERIFIED_STEP | Printed.integral_le_log_add_one_of_exponential_tail; Printed.integral_randomThresholdRadius_le; Printed.integral_randomThresholdRadius_le_log |
| A-sandwich | 1756–1769; appx-sec:smoothing; Lemma2 proof | A_a^{-R_h} subset A_{a,omega} subset A_a^{R_h}; indicator discrepancy is in random boundary layer | UNVERIFIED_STEP | Printed.random_rectangle_sandwich; Printed.endpoint_symmDiff_subset_boundary; Printed.endpoint_indicator_bound; Printed.endpoint_probability_bound |
| A-Jensen | 1768–1770; appx-sec:smoothing; Lemma2 proof | Absolute endpoint discrepancy <= exponential-average absolute sharp discrepancy | UNVERIFIED_STEP | Printed.endpoint_error_le_average_radius |
| A-concentration | 1770–1774; appx-sec:smoothing; Lemma2 proof | Apply actual bounded/Gaussian rectangle concentration at random radius; average to C(E R_h+delta)sqrt L | UNVERIFIED_STEP | Printed.bounded_boundary_layer_le; Printed.gaussian_boundary_layer_le; Printed.lemma2_printed_endpoint_bounds |
| A-final | 1776–1778; eq:endpoint-min | Triangle at both original endpoints and supremum yields Lemma2 | ALTERNATIVE_BYPASS | Printed.smoothingLemma2_printed |
| G-markov | 4733–4736; ben:smoothing; proof | Use E R_h<=C h L, choose d=K h L and derive P(R_h>d)<=1/4 by Markov | ALTERNATIVE_BYPASS | Printed.randomThresholdRadius_markov; Printed.expectedClockCutoff_bad_le |
| G-monotonicity | 4738–4744; ben:smoothing; proof | On R_h<=d, H(a+d1+eta)>=H(a)-C(d+R_h)sqrt L, with reverse-sign analogue | ALTERNATIVE_BYPASS | Printed.gaussian_shifted_probability_bounds; Printed.gaussian_endpoint_expected_width |
| G-average | 4745–4753; ben:smoothing; proof | Bad-event cost -rho; average mixture and absorb discrepancy: D>=rho/2-C(d+E R_h)sqrt L | ALTERNATIVE_BYPASS | Printed.integrate_good_event_variable_bound; Printed.gaussian_endpoint_expected_width; Printed.gaussianEndpointSmoothing_printed |

The mixture is stated at TeX661–680 (`eq:mixture`) and proved again at1797–1808. G.2 proves both sign inequalities at every threshold before taking the supremum; its exact d+R_h error is averaged and Markov uses the actual E R_h.

Logs: /tmp/printed-clock-audit.log; /tmp/printed-endpoint-audit-build.log; /tmp/printed-endpoint-audit.log. All prior result proofs and certificate records were retained.

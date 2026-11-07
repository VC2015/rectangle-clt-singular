# Unnumbered polynomial regime correspondence

Sequence limits use the literal observation-normalized rates. The polynomial-dimension result assumes only p_n=O(n^a), weaker than the printed p_n asymp n^a; the proof derives the necessary logarithmic dimension bound. The sparse q>4 conclusion derives n/L→∞ from K→∞ and R→0 rather than assuming it. The q=4 rate consequence is stated and proved for actual admissible arrays, arbitrary probability spaces and singular covariance.

| TeX | Printed argument | Added declarations |
|---|---|---|
| 1138 | fixed B, n/L→∞: K_q→∞ for 2<q<4 | `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_atTop_below_four` |
| 1141 | exact Bennett-tail/U ratio and its divergence | `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_div_coordinateRate`, `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_dominates_coordinate_below_four` |
| 1148 | K_4=B and uniform absorption of the coordinate term | `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_four`, `RectangleCLT.Companion.SplitV4.Printed.exists_four_moment_absorption_constant`, `RectangleCLT.Companion.SplitV4.Printed.exists_polynomialBennett_rate_four_bound`, `RectangleCLT.Companion.SplitV4.Printed.polynomialMoment_four_uniform_bound` |
| 1161 | fixed B, q>4: K_q→0 and the tail/U ratio vanishes | `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_zero_above_four`, `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_negligible_to_coordinate_above_four` |
| 1163 | polynomial dimensions give O(n^-alpha (log n)^(1+2alpha)) | `RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_exponent_identity`, `RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_polylog_bound`, `RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_isBigO_polylog`, `RectangleCLT.Companion.SplitV4.Printed.polynomial_decay_exponent_gt_quarter` |
| 1170 | q=6 lower/upper rate exponent arithmetic | `RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelope_rates_six` |
| 1497 | fixed-B logK=o(L) when logn=o(L) | `RectangleCLT.Companion.SplitV4.Printed.log_polynomialSparseParameter`, `RectangleCLT.Companion.SplitV4.Printed.sparse_log_dimension_condition_of_log_n` |
| 1499 | q=4: exact sparse-regime three-condition equivalence | `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_four`, `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_four`, `RectangleCLT.Companion.SplitV4.Printed.sparse_regime_four_iff` |
| 1500 | q>4: exact B/(n/L)^(1/2−2/q) growth criterion; full sparse hypotheses force B_n→∞ | `RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_above_four_eq_ratio`, `RectangleCLT.Companion.SplitV4.Printed.coordinateRate_tendsto_zero_under_sparse_conditions`, `RectangleCLT.Companion.SplitV4.Printed.sample_dimension_ratio_tendsto_atTop_under_sparse_conditions`, `RectangleCLT.Companion.SplitV4.Printed.envelope_tendsto_atTop_under_sparse_conditions_above_four` |

Build and strict transitive audit pass: 42 added theorem declarations; standard three axioms only. No incorrect printed passage or remaining omission found in this scope.

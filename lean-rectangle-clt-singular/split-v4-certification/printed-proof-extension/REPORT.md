# Split-V4 printed-proof Lean certification — 7 November 2026

## Certified scope

**The frozen Split-V4 development verifies the 31 proved manuscript statements
and supplies formal counterparts for the substantive printed arguments in the
recorded valid scope. The two derivative-envelope claims in Appendix A require
the explicit qualification “for each integer q ≥ 1.” Their literal q = 0
reading is false and is not certified.**

This extends the result certificate published through
[PR #14](https://github.com/VC2015/HDCLTs/pull/14). That certificate established
the named conclusions, sometimes using alternative proofs. The extension adds
the intermediate claims and composition bridges needed by the printed routes,
while retaining the earlier proofs. It does not change the frozen manuscript.

The [correspondence review](CORRESPONDENCE_REVIEW.md) and
[machine-readable index](coverage.json) account for 254 overlapping passage
records: 253 have checked counterparts following the printed argument, and one
records a formal counterexample and the smallest proposed source repair. These
are review units, not 254 independent theorems. The index binds 811 declaration
references to actual kernel names, expanded types, modules and source hashes.

Completion is expressly qualified: every valid substantive in-paper argument is
accounted for, but the unqualified zeroth-order assertion remains false. The
execution evidence and correspondence review perform different jobs. Lean
checks the formal contracts and proofs; the correspondence review checks their
relationship to the manuscript's hypotheses, intermediate claims and transitions.
No claim is made that Lean parses or certifies the TeX text directly.

The exclusions are:

- **Conjecture 1**, which remains a conjecture.
- The literal **q = 0 derivative-envelope claims**, and the editorial change
  proposed below but not applied to the frozen source.
- Proofs absent from the paper, including an independent proof of the general
  Brascamp–Lieb inequality. The linear consequence actually used is proved
  internally by a disclosed Prékopa argument.
- Yuta's pending **PR #15**, Denis's forthcoming revisions, and any manuscript
  version later than the frozen commit identified below.

The report date is 7 November 2026 in America/New_York. Execution timestamps
below are UTC; publication of some evidence occurred on 8 November UTC.

## Frozen sources and certificate identities

| Object | Exact identity |
| --- | --- |
| Frozen manuscript and handoff | `2bd43fd98d2a8687ccdda3745f9ac8eac96260dd` |
| Manuscript path | `research-rectangle-clt-singular/Unrestricted_CLT-split-V4.tex` |
| Manuscript Git blob | `3dd7ea1a9c92e1d8d7ddfcbb6438b20a65ebc78e` |
| Manuscript SHA-256 | `f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1` |
| Original result proof | `69f89747f4b845491b75cb23134c056bfbcd40f7` |
| Original certificate and evidence | `69363df233f20632d73e953d09981ab495abfb50` |
| PR #14 report head | `efdea14551ce4d57c4b096669e680fbb6b947b8f` |
| Preserved PR #14 merge commit | `e692196356de50c00fcdd66ddad0f3706db0241c` |
| Preserved annotated tag | `split-v4-lean-certified-2026-11-07` |
| Annotated tag object | `bedc3a598a4e7fd6e95f2ba1678008b9989476d6` |
| Printed-proof source | `92896b8a2a4099357486587d17ca1921a3dba161` |
| Printed-proof source tree | `2b1a8ff7f82daa435e3313108bf438b35566c2eb` |
| Printed-proof execution certificate and evidence publication | `0ef13b938895535fe2dcc135b9400688ed97fa61` |

The proof commit adds 202 paths to the preserved merge snapshot and changes no
previously tracked file. The execution-certificate commit is its child and adds
or updates only extension documentation and evidence. This reader report and
its PDF are later publication artifacts; their file history identifies their
publication commit. They do not change the certified Lean source.

The original [report](../REPORT.md) and [PDF](../REPORT.pdf), earlier verification
records, and all 1,184 protected previous-result files remain unchanged. The
[preservation receipt](PRESERVED_CERTIFICATE.json) records the merge parents,
annotated tag, successful PR #14 checks and exclusion of PR #15. The original
tag covers the result certificate; it does not include this later extension.

## All 31 proved statements and their formal anchors

In the table, `S.` abbreviates `RectangleCLT.Companion.SplitV4.`, `P.`
abbreviates `RectangleCLT.Companion.SplitV4.Printed.`, and `C.` abbreviates
`RectangleCLT.Companion.`. Each expands to a fully qualified Lean name.

The result column identifies the preserved named conclusion. The final column
gives representative anchors for its printed argument, allowing the routine
formal adaptations described below. These anchors can be intermediate claims;
the table does not assert that each has the same quantifier order as the named
result. The complete assumptions, compositions and source bindings are recorded
in [coverage.json](coverage.json) and the detailed correspondence report.

<!-- STATEMENT_TABLE_START -->
| Manuscript statement | Preserved result declaration | Representative printed-route anchors |
| --- | --- | --- |
| Theorem 1 | [`S.relativeFourthMomentCLT`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RelativeMain.lean#L87) | [`S.relativeCLT_of_uniform_smooth_comparison`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RelativeSmoothingReduction.lean#L20)<br>[`P.genericRowOperator_fourth_from_signed_hessian`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/InterpolationTriangle.lean#L233)<br>Retained final assembly; B.1 printed Hessian route added. |
| Corollary 1 | [`S.normalizedObservationsCLTExists`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ObservationNormalization.lean#L98) | [`P.normalized_observations_via_current_theorem`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/ObservationTransfer.lean#L14)<br>Current-theorem normalization route. |
| Corollary 2 | [`S.subexponentialRectangleDistanceCLTExists`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SubexponentialTransfer.lean#L41) | [`P.psi1_hypotheses_exponential_at_same_scale`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/OrliczClosure.lean#L73)<br>[`P.orlicz_transfer_via_printed_clipping`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/OrliczTransfer.lean#L118)<br>Exact Orlicz scale and clipping/restoration route. |
| Theorem 2 | [`S.polynomialMomentCLTExists`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/PolynomialMain.lean#L110) | [`P.polynomialMomentCLTExists`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/PolynomialAssembly.lean#L59)<br>Current polynomial-transfer assembly. |
| Corollary 3 | [`S.relativePolyhedralCLT`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RelativeFaceTransfer.lean#L57) | [`P.bounded_polyhedral_via_current_theorem`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/PolyhedralTransfer.lean#L36)<br>[`P.orlicz_polyhedral_via_printed_transfer`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/PolyhedralTransfer.lean#L67)<br>Retained relative projection route; current bounded/Orlicz transfers. |
| Lemma 1 | [`S.lemma_concentration`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Concentration.lean#L136) | [`P.bounded_intrinsic_boundary_fixed_shift_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/BoundedConcentration.lean#L60)<br>[`P.intrinsicGaussianBoundary_printed_mollification`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/GaussianMollification.lean#L299)<br>Printed cube-limit and Gaussian mollification routes. |
| Lemma 2 | [`S.smoothingLemma2`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Smoothing.lean#L190) | [`P.smoothingLemma2_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/EndpointLemma2.lean#L44)<br>Random-logistic radius, layer cake, Jensen and endpoint route. |
| Proposition 1 | [`S.proposition_relative_derivatives`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RelativeDerivativeProposition.lean#L163) | [`S.direct_initialization_bound`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/DirectInitialization.lean#L75)<br>[`P.genericRowOperator_fourth_from_signed_hessian`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/InterpolationTriangle.lean#L233)<br>Retained initialization/seeded assembly; B.1 Hessian bridge added. |
| Proposition 2 | [`S.polynomialEnvelopeTransfer`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ConditionalPolynomialOptimization.lean#L175) | [`P.polynomialEnvelopeTransfer`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/Polynomial.lean#L548)<br>[`P.conditionalGoodKernel_ownGaussian_rectangle_error_le`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/Polynomial.lean#L173)<br>Actual conditional laws and their own-Gaussian shift route. |
| Proposition 3 | [`S.bennettPolynomialCLT_observations`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/BennettPolynomial.lean#L862) | [`S.pairedTailVariance_polynomial_rate`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/BennettPolynomial.lean#L348)<br>[`P.gaussianComparisonWithLargeIncrementRemainders`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LargeIncrement.lean#L254)<br>Retained Bennett regimes/calibration; literal Bernstein input added. |
| Theorem 3 | [`C.skewedTwoPointLowerScale`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/LowerScaleMain.lean#L45) | [`P.skew_exact_product_asymptotic_from_F1`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/SkewLowerProduct.lean#L56)<br>[`P.skew_full_distance_ereal_liminf_from_F1`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/SkewLowerProduct.lean#L133)<br>Current F.1, signed product and full-distance extended-real lower limit. |
| Theorem 4 | [`S.boundedSymmetricLower`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricBoundedLower.lean#L193) | [`P.boundedSymmetricLower_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LowerConstruction.lean#L74)<br>Printed quantile and global maximum comparison. |
| Theorem 5 | [`S.fourthMoment_uniform_constants`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/UniformLowerConstants.lean#L34) | [`P.fourthMomentLower_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LowerConstruction.lean#L152)<br>[`P.fourthMomentOptimal_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LowerOptimal.lean#L75)<br>Printed construction and explicit-coefficient comparison; uniform result endpoint retained. |
| Theorem 6 | [`S.maskedFourthLower`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/MaskedFourthLower.lean#L120) | [`P.maskedFourthLower_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LowerConstruction.lean#L243)<br>Printed masked construction and exact q=4 conversion. |
| Theorem 7 | [`S.denseMoment_uniform_constants`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/UniformLowerConstants.lean#L69) | [`P.printedDenseOptimal_constant_first`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/DenseOptimal.lean#L93)<br>Exact B/2 amplitude and constant-first uniform comparison. |
| Theorem 8 | [`S.sparseMoment_uniform_constants`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/UniformLowerConstants.lean#L103) | [`P.sparseMomentOptimal_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LowerOptimal.lean#L140)<br>Printed sparse construction, fixed q-coefficients and uniform comparison. |
| Lemma A.1 | [`S.lemma_derivative_envelope`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/DerivativeEnvelopeAllOrders.lean#L131) | [`S.logistic_allOrder_local_envelope`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/DerivativeEnvelopeAllOrders.lean#L30)<br>[`P.no_uniform_closedBox_zero_order_averaged_bound`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/EnvelopeZeroOrderSigned.lean#L97)<br>Positive integer orders q≥1 only; literal q=0 counterexample checked. |
| Lemma B.1 | [`S.hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/GenericC4CubicTensor.lean#L89) | [`P.genericRowOperator_fourth_from_signed_hessian`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/InterpolationTriangle.lean#L233)<br>[`P.signed_hessian_fourth_kernel_expectation`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/InterpolationTriangle.lean#L185)<br>Signed Hessian, triangular Fubini and fourth-order kernel route. |
| Lemma B.2 | [`S.lemma_paired_restoration`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Restoration.lean#L129) | [`S.restoration_paired_baseline_product`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RestorationProductBounds.lean#L36)<br>[`S.restoration_fourth_relative_product`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RestorationProductBounds.lean#L120)<br>Retained conditional two-Stein and paired restoration route. |
| Lemma B.3 | [`C.gaussian_mean_relative_to_one_face`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/GaussianEntropy.lean#L203) | [`P.gaussian_one_face_exponential_via_independence`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/GaussianOrthogonalIndependence.lean#L70)<br>[`C.gaussian_mean_relative_to_one_face`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/GaussianEntropy.lean#L203)<br>Actual orthogonal Gaussian independence and retained mean assembly. |
| Lemma B.4 | [`S.exists_logistic_matrix_paper_constant`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticMatrixPaper.lean#L64) | [`P.sector_exists_logistic_matrix_paper_constant`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/MatrixSectorPaper.lean#L50)<br>Full-sector B.5 input, full padded-matrix Fatou, then compression. |
| Lemma B.5 | [`S.averagedGaussianThresholdDerivative_rectangle_bound`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/AveragedThresholdBound.lean#L425) | [`P.averagedGaussianThresholdDerivative_sector_bound`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/RidgeSectorAveraging.lean#L142)<br>[`P.thresholdProjectionRadius_second_third_moments_from_radial_tail`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/ProjectionRadiusMoments.lean#L175)<br>Full angular sector and exact low-dimensional radial-tail moments. |
| Lemma C.1 | [`S.intrinsic_cube_boundary`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/IntrinsicCubeBoundary.lean#L373) | [`P.intrinsic_cube_boundary_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/CubeBoundary.lean#L58)<br>Unique-max perturbation, actual gradients, discrete IBP and radius limit. |
| Lemma E.1 | [`S.expected_maximum_under_envelope_moment`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/EnvelopeMaximum.lean#L152) | [`P.expected_maximum_under_envelope_moment`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/EnvelopeMaximum.lean#L15)<br>Literal Bernstein maximum from tail integration. |
| Lemma F.1 | [`S.uniformScalarModerateTail`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ModerateTailGeneral.lean#L72) | [`P.uniformScalarModerateTail_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LowerModerateGeneral.lean#L44)<br>Copy-based cumulants, actual tilts and strict Laplace integration by parts. |
| Lemma F.2 | [`S.independent_shift_comparison`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ShiftComparison.lean#L259) | [`S.shifted_taylor_bound`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ShiftComparison.lean#L60)<br>[`S.independent_shift_comparison`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ShiftComparison.lean#L259)<br>Retained genuine global Taylor and independent-shift argument. |
| Lemma F.3 | [`S.symmetricFamilyProperties`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricFamilyCertification.lean#L65) | [`S.familyNormalizedObservations_covariance`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricFamilyProperties.lean#L46)<br>[`S.symmetricFamilyProperties`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricFamilyCertification.lean#L65)<br>Retained actual product-law, symmetry, covariance and moment route. |
| Lemma G.1 | [`S.gaussianComparisonWithLargeIncrementRemainders`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LargeIncrementComparison.lean#L531) | [`P.independent_sum_bernstein_mgf`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/Bernstein.lean#L95)<br>[`P.gaussianComparisonWithLargeIncrementRemainders`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/LargeIncrement.lean#L254)<br>Literal Bernstein and retained conditional-copy/time-integral chain. |
| Lemma G.2 | [`S.gaussianEndpointSmoothing`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/GaussianEndpointSmoothing.lean#L286) | [`P.gaussianEndpointSmoothing_printed`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Printed/EndpointGaussian.lean#L289)<br>Expected random width, Markov and monotonicity route. |
| Lemma G.3 | [`S.C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ArraySlepian.lean#L401) | [`S.C4Test.integral_array_summand_paired`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ArraySlepian.lean#L138)<br>[`S.C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ArraySlepian.lean#L401)<br>Retained actual-copy interchange and trapezoidal fourth-order argument. |
| Lemma G.4 | [`S.truncated_bennett_maximum`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/BennettMaximum.lean#L332) | [`S.independent_sum_bennett_log_mgf`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/BennettMaximum.lean#L164)<br>[`S.bounded_vector_bennett_maximum_optimized`](https://github.com/VC2015/HDCLTs/blob/92896b8a2a4099357486587d17ca1921a3dba161/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/BennettMaximum.lean#L291)<br>Retained product Bennett MGF, signs and maximum calculation. |

For Theorem 5, `P.fourthMomentOptimal_printed` is representative support,
not a constant-first replacement endpoint. The printed construction and
comparison use the explicit lower coefficient `1/(4*sqrt(2)*exp(1))` and upper
coefficient `S.polynomialFourthUniformConstant B`, independent of the dimension
sequence. The preserved `S.fourthMoment_uniform_constants` is the exact uniform
result endpoint. The [statement-map audit](REPORT_STATEMENT_MAP.json) records
all 31 endpoints and 50 representative anchors checked against the frozen source.
<!-- STATEMENT_TABLE_END -->

## What the extension checks in the printed proofs

The correspondence record distinguishes three situations. `SAME_ARGUMENT`
means the same mathematical argument, allowing explicit integrability,
conditioning, finite-sum notation and equivalent changes of variables.
`ALTERNATIVE_BYPASS` means a proof establishes the conclusion while bypassing a
substantive printed step. `UNVERIFIED_STEP` identifies a missing counterpart or
a literal assertion requiring repair. Initial and current classifications are
recorded separately. A [baseline-history errata note](BASELINE_CORRESPONDENCE_ERRATA.md)
corrects four initial interpolation classifications; the original hashed owner
fragments are preserved.

The principal additions are:

| Printed argument | Formal coverage added |
| --- | --- |
| Interpolation and paired restoration | The centered value and gradient Hessian-integral identities, signed-Hessian intermediate, genuine triangular Fubini transition, signed kernel and conditional square-root-product Cauchy–Schwarz estimate. These supply the printed route previously bypassed by direct fourth- and third-order Taylor bounds. |
| Logistic displacement and endpoint smoothing | Exact clock tails, union and layer-cake bounds, Markov cutoff, Jensen/Fubini averaging of the random radius, and expected-width control for Lemma 2 and G.2. |
| Matrix and threshold estimates | Actual Gaussian factorization and threshold limits, covariance contraction and signed trace differentiation, polar rank-two tails and radius moments, full angular sectors, projection disjointness, coarea and averaging. A new matrix endpoint carries the sector estimate through dominated convergence and Fatou on the full padded matrix before compression. |
| Cube boundary argument | Finite generic threshold perturbations, the actual Fréchet gradient at a unique maximizer, the convex ramp, discrete integration by parts, closed-layer enlargement and the perturbation limit, including ties and atoms. Gaussian mollification and its limit are also checked. |
| Orlicz and large-increment arguments | Closure at the stated Orlicz scale, clipping and joint Gaussian restoration, the printed Bernstein MGF, maximum and tail integration, conditional-copy and common-point estimates, large-increment biases and matrix remainders, time integration and both Bennett regimes. |
| Moderate deviations and lower constructions | The independent-copy variance identity, cumulant/Taylor and inverse-tilt steps, strict Laplace integration by parts with atoms, the full printed F.1 route, detecting-orthant/product arguments, exact Gaussian quantiles, global shift comparisons, tail moments and uniform integrability. The dense construction uses the printed amplitude B/2. |
| Unnumbered examples and rate consequences | Weighted-sign observations with arbitrary centered sign-vector laws, both fourth-moment matrices and exceptional-weight asymptotics, polynomial dimension rates, logarithmic factors, growing envelopes and the stated regime comparisons. |

The older alternative proofs remain available. Verifying the printed route
does not require replacing the proof value of every old named endpoint: checked
intermediate statements and their composition can establish that route under
the stated assumptions. The new development also has endpoints whose proof
values themselves consume the new routes. Strict dependency guards check
selected such endpoints, including the full-sector matrix argument and the
moderate-deviation inputs to the lower constructions.

One implementation difference remains explicit. In the covariance-contraction
remark at frozen TeX lines 2871–2882, the actual weighted Gaussian potential,
Hessian comparison, probability law and linear-variance application are checked.
The cited external linear Brascamp–Lieb input is kernel-proved using Prékopa.
The paper prints no proof of the general Brascamp–Lieb theorem, and this report
does not claim one. This difference concerns the implementation of that
external input; it does not leave the printed potential/Hessian/application
chain unchecked.

The full-distance lower limits use the conventional **extended-real liminf**
and equivalent eventual positive lower bounds. Actual detecting-orthant real
limits and product asymptotics are proved separately. No additional assumption is imposed that the full-distance liminf is finite.

## The required positive-order manuscript qualification

The local derivative-envelope display at frozen TeX **1848–1852** and the
averaged derivative consequence at **1872–1877** should explicitly restrict the
derivative order to integers **q ≥ 1**. These orders are distinct from the real
moment parameter also denoted q elsewhere in the paper.

The local partition argument uses `θ^k ≤ θ`; it needs a nonempty derivative
partition, hence q ≥ 1. The extension proves all positive derivative orders.
For the literal zeroth-order reading, it proves a counterexample using the
actual one-dimensional two-face smoother for the box [-1,1]. For every positive
bandwidth, F is at least 1/3 on |G| ≤ 1, so its Gaussian expectation is at least
`P(|G| ≤ 1)/3 > 0`. An asserted uniform upper bound proportional to the
bandwidth tends to zero. The checked declaration is
`P.no_uniform_closedBox_zero_order_averaged_bound` in
`Printed/EnvelopeZeroOrderSigned.lean`; a simpler one-face counterexample is
also retained.

The [exact proposed LaTeX replacements](PROPOSED_MANUSCRIPT_REPAIR.md) add
“for every integer q ≥ 1” before the local display and “for each fixed integer
q ≥ 1” before the averaged consequence. They change no positive-order result
or theorem rate. They have not been applied to the frozen manuscript. The
coverage record retains this entry as `UNVERIFIED_STEP` with disposition
`COUNTEREXAMPLE_PROVED_REPAIR_REQUIRED`; it never presents the false claim as
a proved theorem.

## Successful execution and transitive axiom audit

The exact pins are **Lean 4.19.0**, compiler commit `6caaee842e94`,
**Lake 5.0.0-6caaee8**, and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Complete package revisions and the
nine configuration-file hashes are in the
[verification record](PRINTED_PROOF_VERIFICATION.json) and raw run snapshots.

| Evidence | Successful result |
| --- | --- |
| Isolated local proof run | **170/170 required commands**, 7 November 2026, 22:25:16–23:13:33 UTC; detached clean checkout at the frozen proof commit, with private project build caches. |
| Independent GitHub CI | [Run 42420549190](https://github.com/VC2015/HDCLTs/actions/runs/42420549190), attempt 1, job `128547820210`: **170/170 required checkpoint commands**, 22:46:07.804969–23:54:15.666455 UTC. The job completed successfully at 23:55:40 UTC on 7 November. |
| Pristine manuscript baseline in CI | **7/7 required commands**; its separately optional cache command also exited zero, so all eight recorded commands succeeded. |
| Local execution validators | The original frozen-source validator and a separate run on the actual publication copies both passed. |
| Independent-CI comparisons | The downloaded archive and a separate comparison of its actual publication copies passed all source, command-log, declaration and dependency checks. |

The CI API identifies PR head
`92896b8a2a4099357486587d17ca1921a3dba161`, while the actual checkout is
GitHub's synthetic merge `88b6db94075c9f3fcb8cd2d1de062ad4412da1a6`. Its
parents are the preserved merge and the proof commit, and its tree equals the
proof tree exactly. Both identities are preserved; the strict local validator
is not misleadingly applied to a different checkout.

The checks establish:

- Exact source identity for **1,024 Lean files** and **nine configurations**,
  unchanged manuscript and historical records, and clean pinned checkpoint
  dependencies before and after execution.
- Exact agreement between local direct audits, CI direct audits and the CI
  build log for **3,751 preserved dependency records**, **4,724 expanded
  dependency records** and **811 mapped declaration bindings**. Complete
  elaborated types, direct proof/type edges and transitive axioms are compared.
- **973 new printed-theorem records**, **91 implementation modules** and
  fresh execution of all **31 nested route-audit bodies** through the checked
  consolidated audit. The official axiom collector also covers every mapped
  definition and constructor.
- The earlier complete companion audit's **5,757 theorem declarations** remain checked.
  These counts overlap and include generated declarations; they are not counts
  of independent handwritten lemmas.

The only permitted transitive axioms are **`propext`, `Classical.choice` and
`Quot.sound`**. No `sorryAx` or additional assumed mathematical axiom is admitted
by the audits. The kernel evidence verifies the actual Lean contracts; its
relation to the printed mathematics remains the explicit correspondence review.

The cold CI baseline initially had 27 absent package-level Git-dependency
records. Its successful cache step initialized them, and every final checkout
was clean at its unchanged manifest revision. The comparison records that exact
infrastructure transition, along with the workflow's planned cache symlinks and
copied runner. It does not relax either checkpoint snapshot's strict pin or
cleanliness checks. See [CI_REPRODUCTION.md](CI_REPRODUCTION.md).

<!-- ADDITIONAL_CI_START -->
The evidence-publication head also passed
[repeat CI run 42429814215](https://github.com/VC2015/HDCLTs/actions/runs/42429814215),
job `128576012185`, completed **8 November 2026 at 01:14:50 UTC**. Its API head
is `0ef13b938895535fe2dcc135b9400688ed97fa61`; both the pristine-baseline and
checkpoint steps succeeded. The [run response](report-head-ci/github-run.json)
and [job response](report-head-ci/github-jobs.json) preserve this additional
status evidence. The complete raw archive and cross-run declaration comparison
supporting the frozen certificate remain those of proof-source run 42420549190
above. Checks on later report-only commits are separate from that certificate.
<!-- ADDITIONAL_CI_END -->

## Evidence inventory and integrity

| Preserved object | SHA-256 |
| --- | --- |
| [Local run record](logs-checkpoint-92896b8/run.json) | `7f7d9b51c82b948bf6c9be2bfac5ef3739ac97fcb219b57f2aaa9d85243031eb` |
| [Original local validation](CHECKPOINT_VALIDATION.json) | `d7c6af672e6cad33e272f3f1c890ba4d19a5cbecf7a895fcad939cfced02a975` |
| [Local publication-copy validation](CHECKPOINT_PUBLISHED_VALIDATION.json) | `5a998a9d6680a621bce3c235efa71e440e8210aaac06f2cf470f7a0e16ab0bd7` |
| [CI artifact ZIP](logs-ci-42420549190/split-v4-lean-command-evidence-42420549190.zip), artifact `13595718284` | `685835b76c09cbf6b6bd4b2563a57dc60065af1f5a6e3322d010cc9eaeba727b` |
| [CI comparison receipt](ci-evidence-42420549190.json) | `5e0db8ae1028fdb491e93b1664081c4233b3747dfceefc90bec659c3f0ce3e3a` |
| [Independent CI publication-copy validation](CI_PUBLISHED_VALIDATION.json) | `1a6e30b9425d2269126e1930bb058eb4c313f4941047d93486477745d6a15e5f` |

The downloaded ZIP is 10,140,737 bytes and matches GitHub's artifact digest.
The [extraction manifest](logs-ci-42420549190/extraction-manifest.json) binds all
180 regular artifact files to their ZIP members and payload hashes. The
[CI copy manifest](CI_COPY_MANIFEST.json) checks 189 published files, including
raw logs, complete API responses, the archive and reviewed comparison helpers.
The [local copy manifest](CHECKPOINT_COPY_MANIFEST.json) records 178 original
copies. All 170 local command logs remain raw; the duplicate aggregate stream
is stored losslessly as [gzip](CHECKPOINT_RUNNER.log.gz), with original and
stored hashes in the [archive manifest](CHECKPOINT_ARCHIVE_MANIFEST.json).
The [owner-log manifest](logs-owner/manifest.json) preserves 44 earlier logs.

The [verification JSON](PRINTED_PROOF_VERIFICATION.json) records both validators,
the permitted axioms, source/configuration fingerprints, CI provenance and the
qualified completion gate. Its `paper_certified` and
`literal_unqualified_claims_certified` flags remain false; the successful gate
applies to the stated valid scope with the unapplied source repair explicit.
The [report-artifact manifest](REPORT_ARTIFACTS.json) lists the Markdown, PDF
and rendering-asset hashes and renderer versions.

## Reproduction

Use a full clone containing the frozen commits. For the strict local execution,
check out the **proof commit**, rather than an evidence or report commit:

```sh
git clone https://github.com/VC2015/HDCLTs.git HDCLTs-split-v4-printed
cd HDCLTs-split-v4-printed
git checkout --detach 92896b8a2a4099357486587d17ca1921a3dba161
cd lean-rectangle-clt-singular
lake --version
lake env lean --version
lake exe cache get
python3 split-v4-certification/run.py checkpoint --skip-cache \
  --output /tmp/split-v4-printed-reproduction
python3 split-v4-certification/printed-proof-extension/verify_record.py \
  --logs /tmp/split-v4-printed-reproduction \
  --proof-commit 92896b8a2a4099357486587d17ca1921a3dba161 --validate-only
```

Use the pinned Lean toolchain on `PATH` and a new output directory for each run.
The cache command is an optional dependency-download convenience; it does not
replace kernel checking. Keep the committed manifests; do not run `lake update`.
The runner's 170 required commands rebuild and directly execute the complete
dependency, mapped-declaration and consolidated route audits.

To inspect and revalidate the published CI archive, use the evidence commit
`0ef13b938895535fe2dcc135b9400688ed97fa61` or a later report-only head and follow
the exact read-only command in [CI_REPRODUCTION.md](CI_REPRODUCTION.md). That
comparison preserves the synthetic checkout identity and checks exact source
equivalence to the frozen proof. The raw logs and validators are evidence for
the recorded execution, not a replacement for reproducing Lean itself.

From the repository root at a report-publication checkout, generate this PDF
from its Markdown source with:

```sh
cd lean-rectangle-clt-singular
python3 split-v4-certification/printed-proof-extension/build-report.py
```

This last command requires Pandoc, XeLaTeX and the DejaVu fonts; it is a report
rendering command, not a formal proof check.

## Publication and the next manuscript version

[PR #16](https://github.com/VC2015/HDCLTs/pull/16) carries the printed-proof
extension separately from the preserved result-certificate snapshot. At this
report's preparation PR #16 remains unmerged. The original annotated
tag continues to identify exactly the PR #14 merge snapshot. Its report is
available as [Markdown](https://github.com/VC2015/HDCLTs/blob/split-v4-lean-certified-2026-11-07/lean-rectangle-clt-singular/split-v4-certification/REPORT.md)
and [PDF](https://github.com/VC2015/HDCLTs/blob/split-v4-lean-certified-2026-11-07/lean-rectangle-clt-singular/split-v4-certification/REPORT.pdf).

After Yuta's and Denis's revisions, including the proposed positive-order
qualification, a new correspondence check should:

1. Pin the revised TeX/PDF version by commit and source hash. Keep the present
   manuscript, certificates and tag as historical snapshots.
2. Compare every affected statement and proof transition: hypotheses,
   quantifier order, constant dependence, normalization, covariance and matrix
   conventions, moment regimes, thresholds, boundary events and limiting claims.
   Updating printed numbers alone is insufficient.
3. Update the source anchors and declaration map, checking the q ≥ 1 wording
   against the actual positive-order Lean contracts. Review unnumbered examples
   and cross-references as well as the 31 named proved statements.
4. Rebuild with the pinned toolchain, rerun transitive axiom and correspondence
   audits, and issue a separate certificate bound to the revised manuscript and
   proof commits. The present strict validator intentionally checks the old
   frozen hash; a revised certificate must identify its new inputs explicitly.

A successful Lean build alone does not establish correspondence with revised
prose. The final manuscript needs that separate review even when its editorial
changes require no new Lean proof.

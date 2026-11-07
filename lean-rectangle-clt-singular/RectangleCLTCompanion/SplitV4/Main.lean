import RectangleCLTCompanion.SplitV4.ObservationNormalization
import RectangleCLTCompanion.SplitV4.SeedCalibration
import RectangleCLTCompanion.SplitV4.Smoothing
import RectangleCLTCompanion.SplitV4.PolyhedralGeometry
import RectangleCLTCompanion.SplitV4.PairedExchange
import RectangleCLTCompanion.SplitV4.RelativeMoments
import RectangleCLTCompanion.SplitV4.RelativeMomentTransfer
import RectangleCLTCompanion.SplitV4.SubexponentialTransfer
import RectangleCLTCompanion.SplitV4.TimeWeights
import RectangleCLTCompanion.SplitV4.GaussianEndpointSmoothing
import RectangleCLTCompanion.SplitV4.BennettMaximum
import RectangleCLTCompanion.SplitV4.UnrestrictedGaussianComparison
import RectangleCLTCompanion.SplitV4.GaussianFaceTransfer
import RectangleCLTCompanion.SplitV4.OrliczFaceTransfer
import RectangleCLTCompanion.SplitV4.EnvelopeMaximum
import RectangleCLTCompanion.SplitV4.CommonPointFourth
import RectangleCLTCompanion.SplitV4.FourthMaximum
import RectangleCLTCompanion.SplitV4.CommonPointGaussianAverage
import RectangleCLTCompanion.SplitV4.PairedSlepian
import RectangleCLTCompanion.SplitV4.SlepianDerivative
import RectangleCLTCompanion.SplitV4.ProductConditional
import RectangleCLTCompanion.SplitV4.ConditionalTruncation
import RectangleCLTCompanion.SplitV4.CopyProjection
import RectangleCLTCompanion.SplitV4.SmootherC4
import RectangleCLTCompanion.SplitV4.ArraySlepian
import RectangleCLTCompanion.SplitV4.PairedCoefficients
import RectangleCLTCompanion.SplitV4.ConditionalMatrixFluctuation
import RectangleCLTCompanion.SplitV4.PairedMoments
import RectangleCLTCompanion.SplitV4.PairedTailBudgets
import RectangleCLTCompanion.SplitV4.ConditionalTruncationKernel
import RectangleCLTCompanion.SubexponentialMain
import RectangleCLTCompanion.LowerScaleMain
import RectangleCLTCompanion.FactorExistence

/-!
# Split-V4 certification checkpoint

This entry point connects the new split-V4 helpers to the package build.  It
does not assert that the whole manuscript, or any revised analytic proof
chain, has been certified.  A fresh successful execution of `SplitV4/Audit`
is required in addition to type checking this file.

The current statement correspondences are:

* `cor:observations`: `SplitV4.normalizedObservationsRectangleDistanceCLT`
  proves the normalized bounded-observation statement for the actual supremum
  distance, using the older envelope proof. `normalizedObservationsCLTExists`
  fixes its universal constant before dimensions and probability models.
* `cor:subexponential`: `SplitV4.subexponentialRectangleDistanceCLT_psi1`
  transfers `subexponentialCLT_psi1` to the full supremum distance with the
  genuine Orlicz hypothesis and average marginal normalization. Its existence
  endpoint likewise fixes the universal constant before the model.
* `opt:skew-lower`: `skewedTwoPointLowerScale` has the growing-envelope
  quantifiers and lower constant `sqrt 2 / (4 * exp 1)`.
* `ben:smoothing`: `gaussianEndpointSmoothing` applies to arbitrary
  measurable vectors and singular Gaussian endpoints of unit marginal variance.
* `ben:maximum`: `truncated_bennett_maximum` retains the Bennett logarithm
  and the exact omitted-tail coefficient; its zero-variance endpoint is a.e.
* `lem:maximum`: `expected_maximum_under_envelope_moment` proves the
  independent centered-vector bound from genuine variance and envelope moments.
* `ben:paired-interpolation`: `C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths` contains
  the actual conditional copy coefficients and the signed fourth remainder.
  `C4Test.ofContDiff` supplies canonical witnesses for ordinary C4 inputs.
* The envelope specialization of `thm:unrestricted` is `unrestrictedCLT`.
  It does not have a relative fourth-moment parameter and therefore does
  not prove all of Theorem 1.

The unrestricted Gaussian comparison input of Appendix E and the bounded
and Orlicz polyhedral branches are also connected. The paired calculus,
conditional coefficients, fourth-coordinate maximum and common-point
contraction are proof components; their inclusion does not by itself certify
the full paired comparison, polynomial CLT, relative theorem, intrinsic
anti-concentration, or new lower constructions. The statement map retains
these obligations explicitly.
-/

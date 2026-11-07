import RectangleCLTCompanion.SplitV4.ObservationNormalization
import RectangleCLTCompanion.SplitV4.SeedCalibration
import RectangleCLTCompanion.SplitV4.PolyhedralGeometry
import RectangleCLTCompanion.SplitV4.PairedExchange
import RectangleCLTCompanion.SplitV4.RelativeMoments
import RectangleCLTCompanion.SplitV4.SubexponentialTransfer
import RectangleCLTCompanion.SplitV4.TimeWeights
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
* The envelope specialization of `thm:unrestricted` is `unrestrictedCLT`.
  It does not have a relative fourth-moment parameter and therefore does
  not prove all of Theorem 1.

The auxiliary algebra and geometry files are independent proof components.
They do not discharge the new threshold, intrinsic anti-concentration,
paired comparison, Bennett, or lower-construction estimates.  The statement
map and verification checkpoint retain these obligations explicitly.
-/

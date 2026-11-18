import RectangleCLTArxivV1.GaussianRectangleIntrinsic
import Lean.Util.CollectAxioms

#check @RectangleCLTArxivV1.gaussianUnitRowsBoundary_printed
#check @RectangleCLTArxivV1.gaussianUnitRowsMaximum_logarithmic
#check @RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift
#check @RectangleCLTArxivV1.gaussianIntrinsicBoundary_product
#check @RectangleCLTArxivV1.gaussianIntrinsicBoundary_independent_shift
#check @RectangleCLTArxivV1.gaussianFaceLayer_bound

#check @RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift_log_sharp
#check @RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift_logarithmic
#check @RectangleCLTArxivV1.gaussianIntrinsicBoundary_product_logarithmic
#check @RectangleCLTArxivV1.gaussianIntrinsicBoundary_independent_shift_logarithmic
#check @RectangleCLTArxivV1.activeCoordinateNormals_covariance_diagonal
#check @RectangleCLTArxivV1.gaussianRectangleBoundary_intrinsic_fixed_shift
#check @RectangleCLTArxivV1.gaussianRectangleBoundary_intrinsic_product

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``RectangleCLTArxivV1.gaussianUnitRowsBoundary_printed,
    ``RectangleCLTArxivV1.gaussianUnitRowsMaximum_logarithmic,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_product,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_independent_shift,
    ``RectangleCLTArxivV1.gaussianFaceLayer_bound,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift_log_sharp,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_fixed_shift_logarithmic,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_product_logarithmic,
    ``RectangleCLTArxivV1.gaussianIntrinsicBoundary_independent_shift_logarithmic,
    ``RectangleCLTArxivV1.activeCoordinateNormals_covariance_diagonal,
    ``RectangleCLTArxivV1.gaussianRectangleBoundary_intrinsic_fixed_shift,
    ``RectangleCLTArxivV1.gaussianRectangleBoundary_intrinsic_product] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"

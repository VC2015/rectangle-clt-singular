import RectangleCLTArxivV1.PolyhedralIntrinsicMain
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_coordinate_memLp_two,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_centered,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_covariance,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_average_second,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected_envelope_moment,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.projected,
    ``RectangleCLTArxivV1.PolynomialFourthHypotheses.toArchived,
    ``RectangleCLTArxivV1.PolynomialFourthHypotheses.projected,
    ``RectangleCLTArxivV1.polyhedralFaceVariance_nonneg,
    ``RectangleCLTArxivV1.positivePolyhedralFaceIndex_injective,
    ``RectangleCLTArxivV1.positivePolyhedralFaceIndex_range,
    ``RectangleCLTArxivV1.positivePolyhedralFaceIndex_variance_pos,
    ``RectangleCLTArxivV1.omittedPolyhedralFace_variance_zero,
    ``RectangleCLTArxivV1.positivePolyhedralFaceScale_pos,
    ``RectangleCLTArxivV1.positivePolyhedralFaceScale_sq,
    ``RectangleCLTArxivV1.polyhedralDistance_eq_positive_faces,
    ``RectangleCLTArxivV1.polyhedralIntrinsicWidth_zero_of_no_positive_faces,
    ``RectangleCLTArxivV1.polyhedralDistance_zero_of_no_positive_faces,
    ``RectangleCLTArxivV1.PolyhedralNormalBound.positive_faces,
    ``RectangleCLTArxivV1.positivePolyhedralFace_variance_identity,
    ``RectangleCLTArxivV1.positivePolyhedralFaceCount_le,
    ``RectangleCLTArxivV1.projectedGaussian_factor_exists,
    ``RectangleCLTArxivV1.polyhedralIntrinsicWidth_le,
    ``RectangleCLTArxivV1.boundedPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.boundedPolyhedralCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.boundedPolyhedralEnvelopeCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.polynomialPolyhedralEnvelope_inputs,
    ``RectangleCLTArxivV1.polynomialPolyhedralWidth_le,
    ``RectangleCLTArxivV1.polynomialPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.PolynomialEnvelopeHypotheses.normalized_sum_L2_centered,
    ``RectangleCLTArxivV1.polynomialPolyhedralCLT_all_faces_intrinsic,
    ``RectangleCLTArxivV1.polynomialPolyhedralWidth_all_faces_le,
    ``RectangleCLTArxivV1.psi1Independent_projected_exact,
    ``RectangleCLTArxivV1.orliczPolyhedralCLT_intrinsic,
    ``RectangleCLTArxivV1.orliczPolyhedralCLT_intrinsic_all_faces,
    ``RectangleCLTArxivV1.corollary_3_bounded_orlicz_intrinsic,
    ``RectangleCLTArxivV1.corollary_3_intrinsic]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"

import RectangleCLTArxivV1.SupplementalHNonsimplePrintedGreen
import RectangleCLTArxivV1.SupplementalHNonsimpleFacePrintedSpherical
import RectangleCLTArxivV1.SupplementalHNonsimpleSquareBalance

/-! The general printed identities applied to the genuine square cone.
Its vertex has four actual active facets and normal rank three. These
closed examples have no genericity or analytic supplier hypotheses. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators InnerProductSpace
noncomputable section

theorem nonsimpleSquare_printed_ridge_Green :
    hardGaussianWeightedRidgeIntegral nonsimpleSquareNormals 0 =
      (∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals nonsimpleSquareNormals) 0 2,
        nonsimpleActualRidgeLeading nonsimpleSquareNormals 0 R) -
        nonsimpleActualThirdBoundary nonsimpleSquareNormals 0 := by
  exact hardGaussianWeightedRidgeIntegral_Green_actualFaces_compact _ _
    nonsimpleSquare_strictInterior nonsimpleSquare_irredundant nonsimpleSquareNormals_unit

theorem nonsimpleSquare_actualVertex_printed_spherical_balance :
    nonsimpleActualConormalSum nonsimpleSquareNormals 0 nonsimpleSquareActualVertex =
      nonsimpleFaceCoordinateLift (nonsimpleNativeNormals nonsimpleSquareNormals) 0
        nonsimpleSquareActualVertex
        ((2 : ℝ) • ∫ ω in supplementalHSphericalSection
          (nonsimpleFaceCoordinateCone nonsimpleSquareNormals 0 nonsimpleSquareActualVertex),
          ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) := by
  exact nonsimpleActualConormalSum_eq_spherical_vector _ _ nonsimpleSquare_strictInterior
    nonsimpleSquare_irredundant nonsimpleSquareNormals_unit nonsimpleSquareActualVertex

theorem nonsimpleSquare_actualVertex_printed_spherical_norm_bound :
    ‖nonsimpleActualConormalSum nonsimpleSquareNormals 0 nonsimpleSquareActualVertex‖ ≤
      2 * (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real
        (supplementalHSphericalSection
          (nonsimpleFaceCoordinateCone nonsimpleSquareNormals 0 nonsimpleSquareActualVertex)) := by
  exact nonsimpleActualConormalSum_norm_le_spherical_area _ _ nonsimpleSquare_strictInterior
    nonsimpleSquare_irredundant nonsimpleSquareNormals_unit nonsimpleSquareActualVertex

end
end RectangleCLTArxivV1

import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoordinateBalance

/-! Supplier-free arbitrary-edge spherical balance for every actual
codimension-three face of the original irredundant polyhedron. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
local notation "uE" => (fun j => projectionEuclideanVector (u j))
local notation "V" => nonsimpleFaceCoordinateNormals uE b H
local notation "N" => nonsimpleRidgeCoordinateConormal uE b H
local notation "A" => nonsimpleRidgeCoordinateLeft u b hi hw hu H
local notation "B" => nonsimpleRidgeCoordinateRight u b hi hw hu H
local notation "Ridges" => NonsimpleRidgeAt uE b H

def nonsimpleFaceCoordinateCone : Set E3 := sphericalPolygonGeneratedCone V

def nonsimpleRidgeOriginalAngle (e : Fin (Fintype.card Ridges)) : ℝ :=
  let P := nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)
  Real.arccos (faceDot (u P.1.1) (u P.1.2))

theorem nonsimpleRidgeCoordinate_angle_original (e : Fin (Fintype.card Ridges)) :
    Real.arccos ⟪V (A e),V (B e)⟫_ℝ=nonsimpleRidgeOriginalAngle u b hi hw hu H e := by
  rw [nonsimpleFaceCoordinateNormals_inner,nonsimpleRidgeCoordinateLeft_original,
    nonsimpleRidgeCoordinateRight_original]
  unfold nonsimpleRidgeOriginalAngle
  dsimp only
  congr 1
  exact (faceDot_eq_euclidean_inner _ _).symm

include hi hw hu in
theorem nonsimpleFaceCoordinateCone_mem_iff_incident_halfspaces (x : E3) :
    x∈nonsimpleFaceCoordinateCone u b H ↔ ∀ e,0≤⟪N e,x⟫_ℝ := by
  obtain ⟨d,hd⟩ := nonsimpleFaceCoordinateNormals_exists_strictPolar uE b H
    (nonsimpleOriginal_strictInterior_euclidean u b hi)
  exact sphericalPolygonGeneratedCone_mem_iff_nonzero_incident_halfspaces V
    (nonsimpleFaceCoordinateNormals_span uE b H) d hd N
    (fun e i => by simpa only [real_inner_comm] using nonsimpleRidgeCoordinateConormal_nonneg uE b H e i)
    (nonsimpleOriginal_coordinate_nonzero_coverage u b hi hw hu H) x

include hi hw hu in
theorem nonsimpleFaceCoordinateCone_eq_incident_halfspaces :
    nonsimpleFaceCoordinateCone u b H={x : E3 | ∀ e,⟪-N e,x⟫_ℝ≤0} := by
  ext x
  simpa only [Set.mem_setOf_eq,inner_neg_left,neg_nonpos] using
    nonsimpleFaceCoordinateCone_mem_iff_incident_halfspaces u b hi hw hu H x

include hi hw hu in
theorem nonsimpleFaceCoordinate_incident_nonparallel :
    PairwiseNonparallelNormals (sphericalPolygonOutwardNormals N) :=
  sphericalPolygonOutwardNormals_nonparallel V A B N
    (nonsimpleRidgeCoordinate_pair_distinct u b hi hw hu H)
    (nonsimpleRidgeCoordinate_pairs_injective u b hi hw hu H)
    (nonsimpleOriginal_coordinateConormal_zero u b hi hw hu H)
    (nonsimpleOriginal_coordinateConormal_strict u b hi hw hu H)

theorem nonsimpleFaceCoordinateCone_facet_angle (e : Fin (Fintype.card Ridges)) :
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).toSphere.real
      (supplementalHSphericalSection (sphericalPolygonFacetChart
        (nonsimpleFaceCoordinateCone u b H) (sphericalPolygonOutwardNormals N e)))=
      nonsimpleRidgeOriginalAngle u b hi hw hu H e := by
  rw [←nonsimpleRidgeCoordinate_angle_original u b hi hw hu H e]
  exact sphericalPolygon_generated_facet_angular_area V A B N
    (nonsimpleOriginal_coordinateNormals_unit u b hu H)
    (nonsimpleRidgeCoordinateConormal_unit uE b H)
    (nonsimpleRidgeCoordinate_pair_distinct u b hi hw hu H)
    (nonsimpleOriginal_coordinateConormal_zero u b hi hw hu H)
    (nonsimpleOriginal_coordinateConormal_strict u b hi hw hu H)
    (nonsimpleOriginal_coordinateNormals_pair_plus_ne u b hi hw hu H)
    (nonsimpleOriginal_coordinateNormals_pair_minus_ne u b hi hw hu H) e

theorem nonsimpleFaceCoordinate_spherical_balance :
    (∑ e,nonsimpleRidgeOriginalAngle u b hi hw hu H e • N e)=
      (2 : ℝ) • ∫ ω in supplementalHSphericalSection (nonsimpleFaceCoordinateCone u b H),
        ω.1 ∂(volume : Measure E3).toSphere := by
  obtain ⟨d,hd⟩ := nonsimpleFaceCoordinateNormals_exists_strictPolar uE b H
    (nonsimpleOriginal_strictInterior_euclidean u b hi)
  simp_rw [←nonsimpleRidgeCoordinate_angle_original u b hi hw hu H]
  exact sphericalPolygon_nonzero_incident_balance V A B N
    (nonsimpleFaceCoordinateNormals_span uE b H) d hd
    (nonsimpleOriginal_coordinateNormals_unit u b hu H)
    (nonsimpleRidgeCoordinateConormal_unit uE b H)
    (nonsimpleRidgeCoordinate_pair_distinct u b hi hw hu H)
    (nonsimpleRidgeCoordinate_pairs_injective u b hi hw hu H)
    (nonsimpleOriginal_coordinateConormal_zero u b hi hw hu H)
    (nonsimpleOriginal_coordinateConormal_strict u b hi hw hu H)
    (nonsimpleOriginal_coordinateNormals_pair_plus_ne u b hi hw hu H)
    (nonsimpleOriginal_coordinateNormals_pair_minus_ne u b hi hw hu H)
    (nonsimpleOriginal_coordinate_nonzero_coverage u b hi hw hu H)

theorem nonsimpleFaceCoordinate_spherical_balance_norm_le :
    ‖∑ e,nonsimpleRidgeOriginalAngle u b hi hw hu H e • N e‖≤
      2*(volume : Measure E3).toSphere.real
        (supplementalHSphericalSection (nonsimpleFaceCoordinateCone u b H)) := by
  rw [nonsimpleFaceCoordinate_spherical_balance u b hi hw hu H,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left (supplementalH_spherical_vectorIntegral_norm_le volume _)
    (by norm_num)

end
end RectangleCLTArxivV1

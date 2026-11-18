import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoordinateTransport
import RectangleCLTArxivV1.SupplementalHNonsimplePrintedQuantities

/-! Choice-free printed actual-ridge angles and full actual-face signed
conormal sums match the proved arbitrary-edge spherical vector. -/
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
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
local notation "uE" => nonsimpleNativeNormals u
local notation "Ridges" => NonsimpleRidgeAt uE b H

theorem nonsimpleRidgeOriginalAngle_eq_actual (e : Fin (Fintype.card Ridges)) :
    nonsimpleRidgeOriginalAngle u b hi hw hu H e=
      nonsimpleActualRidgeAngle u b (nonsimpleFaceRidgeIndex uE b H e).1 := by
  let P := nonsimpleActualRidgePair u b hi hw hu H (nonsimpleFaceRidgeIndex uE b H e)
  exact (nonsimpleActualRidgeAngle_eq_pair u b (nonsimpleFaceRidgeIndex uE b H e).1
    P.1.1 P.1.2 P.2.1 P.2.2).symm

theorem nonsimpleActualConormalSum_eq_coordinate_sum :
    nonsimpleActualConormalSum u b H=
      ∑ e : Fin (Fintype.card Ridges),nonsimpleRidgeOriginalAngle u b hi hw hu H e •
        nonsimpleIncidentConormal uE b H (nonsimpleFaceRidgeIndex uE b H e) := by
  classical
  let p : NonsimpleFaceIndex uE b 2 → Prop := fun R => R.1⊆H.1
  let f : NonsimpleFaceIndex uE b 2 → EuclideanSpace ℝ (Fin r) :=
    fun R => nonsimpleActualRidgeAngle u b R • nonsimpleActualIncidenceConormal u b R H
  have hsplit := Fintype.sum_subtype_add_sum_subtype p f
  have hzero : (∑ I : {R : NonsimpleFaceIndex uE b 2 // ¬p R},f I.1)=0 := by
    apply Finset.sum_eq_zero
    intro I _
    dsimp only [f]
    rw [nonsimpleActualIncidenceConormal_of_not_incident u b I.1 H I.2,smul_zero]
  have hfirst : nonsimpleActualConormalSum u b H=∑ I : Ridges,
      nonsimpleActualRidgeAngle u b I.1 • nonsimpleIncidentConormal uE b H I := by
    change (∑ R,f R)=_
    rw [←hsplit,hzero,add_zero]
    apply Finset.sum_congr (by ext I; simp)
    intro I _
    dsimp only [f]
    rw [nonsimpleActualIncidenceConormal_of_incident u b I.1 H I.2]
  calc
    nonsimpleActualConormalSum u b H=
        ∑ I : Ridges,nonsimpleActualRidgeAngle u b I.1 • nonsimpleIncidentConormal uE b H I := hfirst
    _=∑ e : Fin (Fintype.card Ridges),nonsimpleActualRidgeAngle u b (nonsimpleFaceRidgeIndex uE b H e).1 •
        nonsimpleIncidentConormal uE b H (nonsimpleFaceRidgeIndex uE b H e) :=
      ((nonsimpleFaceRidgeIndex uE b H).sum_comp
        (fun I => nonsimpleActualRidgeAngle u b I.1 • nonsimpleIncidentConormal uE b H I)).symm
    _=_ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [nonsimpleRidgeOriginalAngle_eq_actual]

include hi hw hu in
theorem nonsimpleActualConormalSum_eq_spherical_vector :
    nonsimpleActualConormalSum u b H=nonsimpleFaceCoordinateLift uE b H
      ((2 : ℝ) • ∫ ω in supplementalHSphericalSection (nonsimpleFaceCoordinateCone u b H),
        ω.1 ∂(volume : Measure E3).toSphere) := by
  rw [nonsimpleActualConormalSum_eq_coordinate_sum u b hi hw hu H]
  exact nonsimpleFaceNative_spherical_balance u b hi hw hu H

include hi hw hu in
theorem nonsimpleActualConormalSum_norm_le_spherical_area :
    ‖nonsimpleActualConormalSum u b H‖≤
      2*(volume : Measure E3).toSphere.real
        (supplementalHSphericalSection (nonsimpleFaceCoordinateCone u b H)) := by
  rw [nonsimpleActualConormalSum_eq_coordinate_sum u b hi hw hu H]
  exact nonsimpleFaceNative_spherical_balance_norm_le u b hi hw hu H

end
end RectangleCLTArxivV1

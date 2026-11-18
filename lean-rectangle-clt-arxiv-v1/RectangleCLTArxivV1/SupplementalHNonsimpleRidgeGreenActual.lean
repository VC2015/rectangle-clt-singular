import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenSelected
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSelectedBijection
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeEnumeration

/-! Pointwise Gauss--Green on an actual ridge, summed over all complete
codimension-three cofaces exactly once. The finite bijection is the
actual selected-facet/coface correspondence, including nonsimple faces. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ActualRidgeFacetPresentation.native_Green_actualFaces {m n : ℕ}
    {u : Fin m → Vector (n+1)} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k, vectorNormSq (u k) = 1) (hjl : j ≠ l)
    (hridge : HasStrictRidgeInterior u b j l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hR : R.1 = {j,l}) :
    hardGaussianSignedRidgeTerm u b j l = nonsimpleActualRidgeLeading u b R -
      ∑ H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3,
        nonsimpleActualRidgeAngle u b R *
          (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
            nonsimpleActualIncidenceConormal u b R H⟫_ℝ * nonsimpleActualGaussianMass u b H) := by
  classical
  let p : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3 → Prop :=
    fun H => j ∈ H.1 ∧ l ∈ H.1
  let f : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3 → ℝ :=
    fun H => nonsimpleActualRidgeAngle u b R *
      (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
        nonsimpleActualIncidenceConormal u b R H⟫_ℝ * nonsimpleActualGaussianMass u b H)
  have hsplit := Fintype.sum_subtype_add_sum_subtype p f
  have hzero : (∑ H : {H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3 // ¬p H},
      f H.1) = 0 := by
    apply Finset.sum_eq_zero
    intro H _
    have hn : ¬R.1 ⊆ H.1.1 := by
      intro hs
      apply H.2
      exact ⟨hs (by simp [hR]),hs (by simp [hR])⟩
    dsimp only [f]
    rw [nonsimpleActualIncidenceConormal_of_not_incident u b R H.1 hn,
      inner_zero_right, zero_mul, mul_zero]
  have hsum : (∑ i, f (P.selectedActualFace hi hw hu hjl hridge i)) = ∑ H, f H := by
    have heq : (∑ i, f (P.selectedActualFace hi hw hu hjl hridge i)) =
        ∑ H : {H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3 // p H}, f H.1 := by
      calc
        _ = ∑ H : NonsimpleFacesAtPair u b j l, f H.1 :=
          P.sum_selectedActualFace hi hw hu hjl hridge (fun H => f H.1)
        _ = _ := by
          apply Finset.sum_congr (by ext H; simp)
          intro H _
          rfl
    rw [←hsplit,hzero,add_zero]
    exact heq
  rw [P.native_Green_selected_actualFaces hi hw hu hjl hridge R hR]
  change _ - (∑ i, f (P.selectedActualFace hi hw hu hjl hridge i)) = _ - ∑ H, f H
  rw [hsum]

/-- The actual pointwise ridge Green identity. It has no selected
presentation, generic-threshold, limiting, or target-identity premise. -/
theorem hardGaussianSignedRidgeTerm_Green_actualFace {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k, vectorNormSq (u k) = 1) (j l : Fin m) (hjl : j ≠ l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hR : R.1 = {j,l}) :
    hardGaussianSignedRidgeTerm u b j l = nonsimpleActualRidgeLeading u b R -
      ∑ H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3,
        nonsimpleActualRidgeAngle u b R *
          (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
            nonsimpleActualIncidenceConormal u b R H⟫_ℝ * nonsimpleActualGaussianMass u b H) := by
  have hridge := (strictRidgeInterior_iff_actual_ridge_face u b hi hw hu j l hjl).mpr ⟨R,hR⟩
  obtain ⟨P⟩ := actualFacet_exists_ridgeFacetPresentation u b hi hw hu j l hjl hridge
  exact P.native_Green_actualFaces hi hw hu hjl hridge R hR

end
end RectangleCLTArxivV1

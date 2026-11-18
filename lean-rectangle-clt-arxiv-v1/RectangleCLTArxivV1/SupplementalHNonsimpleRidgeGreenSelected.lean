import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenCanonical
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenLeading
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceSelected

/-! The local pointwise Green identity expressed in complete actual
face data. At this stage the sum is over the irredundant selected tangent
facets; its geometric bijection with all incident faces is separate. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ActualRidgeFacetPresentation.boundaryCoefficient_eq_selectedActualFace {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k, vectorNormSq (u k) = 1) (hjl : j ≠ l)
    (hridge : HasStrictRidgeInterior u b j l) (i : Fin P.count)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hR : R.1 = {j,l}) :
    P.signedDistance i * (hardGaussianRidgeNormalWeight u b j l * P.boundaryMass i) =
      nonsimpleActualRidgeAngle u b R *
        (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b
            (P.selectedActualFace hi hw hu hjl hridge i),
          nonsimpleActualIncidenceConormal u b R
            (P.selectedActualFace hi hw hu hjl hridge i)⟫_ℝ *
          nonsimpleActualGaussianMass u b (P.selectedActualFace hi hw hu hjl hridge i)) := by
  classical
  let H := P.selectedActualFace hi hw hu hjl hridge i
  have hm := P.selectedActualFace_supporting_indices hi hw hu hjl hridge i
  have hinc : R.1 ⊆ H.1 := by
    rw [hR]
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hm.1
    · have heq := Finset.mem_singleton.mp hk
      simpa only [heq] using hm.2.1
  have hridge' := hridge
  obtain ⟨x,hxj,hxl,_⟩ := hridge'
  have hp := actualFacet_pair_support_nonparallel u b hi hw j l hjl x hxj hxl
  have hc := P.boundaryCoefficient_eq_actualIncidence (hu j) (hu l) hp i H
    ⟨R,hinc⟩ hR hm.2.2
  rw [nonsimpleActualRidgeAngle_eq_pair u b R j l hjl hR,
    nonsimpleActualIncidenceConormal_of_incident u b R H hinc]
  exact hc

/-- Genuine local Gauss--Green at one actual ridge, with canonical
complete-face masses and conormals. No generic-threshold or almost-everywhere
assumption enters this identity. -/
theorem ActualRidgeFacetPresentation.native_Green_selected_actualFaces {m n : ℕ}
    {u : Fin m → Vector (n+1)} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ k, vectorNormSq (u k) = 1) (hjl : j ≠ l)
    (hridge : HasStrictRidgeInterior u b j l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hR : R.1 = {j,l}) :
    hardGaussianSignedRidgeTerm u b j l = nonsimpleActualRidgeLeading u b R -
      ∑ i, nonsimpleActualRidgeAngle u b R *
        (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b
            (P.selectedActualFace hi hw hu hjl hridge i),
          nonsimpleActualIncidenceConormal u b R
            (P.selectedActualFace hi hw hu hjl hridge i)⟫_ℝ *
          nonsimpleActualGaussianMass u b (P.selectedActualFace hi hw hu hjl hridge i)) := by
  classical
  have hridge' := hridge
  obtain ⟨x,hxj,hxl,_⟩ := hridge'
  have hp := actualFacet_pair_support_nonparallel u b hi hw j l hjl x hxj hxl
  rw [P.native_Green (hu j) (hu l) hp]
  have hleading : hardGaussianRidgeLeadingTerm u b j l = nonsimpleActualRidgeLeading u b R := by
    rw [hardGaussianRidgeLeadingTerm_eq_actualFace u b j l (hu j) (hu l) hp R hR,
      nonsimpleActualRidgeLeading, nonsimpleActualRidgeAngle_eq_pair u b R j l hjl hR]
  rw [hleading]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact P.boundaryCoefficient_eq_selectedActualFace hi hw hu hjl hridge i R hR

end
end RectangleCLTArxivV1

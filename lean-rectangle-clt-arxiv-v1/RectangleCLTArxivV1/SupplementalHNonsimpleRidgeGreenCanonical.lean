import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenActualMass
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenConormal
import RectangleCLTArxivV1.SupplementalHNonsimplePrintedQuantities

/-! A selected tangent facet carries the actual incidence conormal and
signed Gaussian boundary coefficient of its complete codimension-three
face. The complete active set may contain arbitrarily many facets. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ActualRidgeFacetPresentation.outwardConormal_eq_actualIncidence {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (I : NonsimpleRidgeAt (nonsimpleNativeNormals u) b H)
    (hR : I.1.1 = {j,l}) (hk : P.index i ∈ H.1) :
    (WithLp.equiv 2 (Vector r)).symm (P.outwardConormal i) =
      nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H I := by
  classical
  have hjR : j ∈ I.1.1 := by simp [hR]
  have hlR : l ∈ I.1.1 := by simp [hR]
  have hkR : P.index i ∉ I.1.1 := by
    rw [hR]
    have hmem := P.retained i
    have hkl := (Finset.mem_erase.mp hmem).1
    have hkj := (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).1
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hkj,hkl⟩
  have hjc : ⟪nonsimpleNativeNormals u j,
      nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H I⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact nonsimpleIncidentConormal_zero_on_ridge _ _ H I j hjR
  have hlc : ⟪nonsimpleNativeNormals u l,
      nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H I⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact nonsimpleIncidentConormal_zero_on_ridge _ _ H I l hlR
  apply Eq.symm
  apply P.outwardConormal_unique hu hv hp i _
    (nonsimpleIncidentConormal_unit _ _ H I)
  · rw [P.nativeBoundaryFrame_span_actualFace hu hv hp i H (I.2 hjR) (I.2 hlR) hk]
    exact nonsimpleIncidentConormal_mem _ _ H I
  · change ⟪‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖⁻¹ •
        (nonsimpleNativeNormals u j + nonsimpleNativeNormals u l),
        nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H I⟫_ℝ = 0
    rw [inner_smul_left, conj_trivial, inner_add_left, hjc, hlc, zero_add, mul_zero]
  · change ⟪‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖⁻¹ •
        (nonsimpleNativeNormals u j - nonsimpleNativeNormals u l),
        nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H I⟫_ℝ = 0
    rw [inner_smul_left, conj_trivial, inner_sub_left, hjc, hlc, sub_zero, mul_zero]
  · rw [real_inner_comm]
    exact nonsimpleIncidentConormal_strict_on_other _ _ H I (P.index i) hk hkR

theorem ActualRidgeFacetPresentation.signedDistance_eq_actualIncidence {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (I : NonsimpleRidgeAt (nonsimpleNativeNormals u) b H)
    (hR : I.1.1 = {j,l}) (hk : P.index i ∈ H.1) :
    P.signedDistance i =
      ⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
        nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H I⟫_ℝ := by
  have hj : j ∈ H.1 := I.2 (by simp [hR])
  have hl : l ∈ H.1 := I.2 (by simp [hR])
  let x : Vector r := (WithLp.equiv 2 (Vector r))
    (nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H)
  have hxj : faceDot (u j) x = b j := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceNormalPoint_levels _ _ H j hj
  have hxl : faceDot (u l) x = b l := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceNormalPoint_levels _ _ H l hl
  have hxk : faceDot (u (P.index i)) x = b (P.index i) := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceNormalPoint_levels _ _ H (P.index i) hk
  obtain ⟨he,hf⟩ := thresholdPair_frame_levels_of_support u b j l x hp.1 hp.2 hxj hxl
  rw [P.signedDistance_eq_support hu hv i x he hf hxk, faceDot_eq_euclidean_inner]
  change ⟪(WithLp.equiv 2 (Vector r)).symm (P.outwardConormal i),
    nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H⟫_ℝ = _
  rw [P.outwardConormal_eq_actualIncidence hu hv hp i H I hR hk, real_inner_comm]

/-- The actual boundary coefficient in the native pair Green identity.
The angle, signed conormal support and complete-face mass are derived
from the selected exact presentation rather than supplied as identities. -/
theorem ActualRidgeFacetPresentation.boundaryCoefficient_eq_actualIncidence {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (P : ActualRidgeFacetPresentation u b j l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) (i : Fin P.count)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3)
    (I : NonsimpleRidgeAt (nonsimpleNativeNormals u) b H)
    (hR : I.1.1 = {j,l}) (hk : P.index i ∈ H.1) :
    P.signedDistance i * (hardGaussianRidgeNormalWeight u b j l * P.boundaryMass i) =
      Real.arccos (faceDot (u j) (u l)) *
        (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
          nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H I⟫_ℝ *
          nonsimpleActualGaussianMass u b H) := by
  have hj : j ∈ H.1 := I.2 (by simp [hR])
  have hl : l ∈ H.1 := I.2 (by simp [hR])
  rw [P.signedDistance_eq_actualIncidence hu hv hp i H I hR hk]
  have hm := P.normalDensity_mul_boundaryMass_eq_actualFaceMass hu hv hp i H hj hl hk
  dsimp only [hardGaussianRidgeNormalWeight]
  rw [← hm]
  ring

end
end RectangleCLTArxivV1

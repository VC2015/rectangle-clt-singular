import RectangleCLTArxivV1.SupplementalHCubicMatrixEstimate
import RectangleCLTArxivV1.SupplementalHInputShift

/-! The cubic proposition for every rectangular factor and deterministic
translation. Singular covariance and repeated normals are permitted. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem proposition_H1_cubic_matrix_rectangular {p r K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0<C₀) (hδ : 0≤δ) (hκ : 0<κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+1) → Face p, symmetricNuclearNorm
      (supplementalHCubicSelectorScore s (σ • A) (A.mulVec x) α (selectorFaceNormal A (α 0))) ∂ν) ≤
      supplementalHCubicMatrixConstant C₀^(K+2)*s.bandwidth*κ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  cases r with
  | zero =>
      have ht := hunit ⟨0,by omega⟩
      norm_num [vectorNormSq] at ht
  | succ n => exact proposition_H1_cubic_matrix hp ν s A hC₀ hδ hκ hσ hunit hδh hc hδσ

/-- Uniform deterministic threshold shifts are part of the actual
physical-base theorem, rather than a support-reconstruction premise. -/
theorem proposition_H1_cubic_matrix_shifted {p r K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (z : Vector p) {C₀ δ κ σ : ℝ}
    (hC₀ : 0<C₀) (hδ : 0≤δ) (hκ : 0<κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => z+A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+1) → Face p, symmetricNuclearNorm
      (supplementalHCubicSelectorScore s (σ • A) (z+A.mulVec x) α (selectorFaceNormal A (α 0))) ∂ν) ≤
      supplementalHCubicMatrixConstant C₀^(K+2)*s.bandwidth*κ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  have hR : Measurable (fun x : Vector r => z+A.mulVec x) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hrec : ∀ᵐ x ∂ν, z+A.mulVec x=z+A.mulVec (id x) := ae_of_all _ (fun _ => rfl)
  have hc0 := intrinsicRectangleConcentration_remove_ae_shift ν id measurable_id
    (fun x => z+A.mulVec x) hR A z hrec hc
  simp only [Measure.map_id] at hc0
  have h := proposition_H1_cubic_matrix_rectangular (K := K) hp ν (supplementalHInputShift s z) A
    hC₀ hδ hκ hσ hunit hδh hc0 hδσ
  calc
    _ = (∫ x, ∑ α : Fin (K+1) → Face p, symmetricNuclearNorm
        (supplementalHCubicSelectorScore (supplementalHInputShift s z) (σ • A) (A.mulVec x) α
          (selectorFaceNormal A (α 0))) ∂ν) := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      apply Finset.sum_congr rfl
      intro α _
      exact congrArg symmetricNuclearNorm
        (supplementalHInputShift_cubicScore s z (A.mulVec x) (σ • A) α (selectorFaceNormal A (α 0))).symm
    _ ≤ _ := h

end
end RectangleCLTArxivV1

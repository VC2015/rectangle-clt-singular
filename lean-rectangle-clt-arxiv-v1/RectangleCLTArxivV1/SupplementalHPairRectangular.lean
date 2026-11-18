import RectangleCLTArxivV1.SupplementalHPairMatrixEstimate
import RectangleCLTArxivV1.SupplementalHInputShift

/-! The full angle-weighted pair proposition for arbitrary rectangular
factors and deterministic translations, retaining every original face. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem supplementalHInputShift_pairScore {p r q : ℕ}
    (s : FaceSmoother p) (z v : Vector p) (M : Matrix (Fin p) (Fin r) ℝ)
    (α : Fin q → Face p) :
    selectorGaussianScore (supplementalHInputShift s z) M (fun _ : Unit => v) α ()=
      selectorGaussianScore s M (fun _ : Unit => z+v) α () := by
  ext j k
  unfold selectorGaussianScore weightedScore
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    change (g j*g k-(if j=k then 1 else 0))*
      selectorWeight (supplementalHInputShift s z) α (M.mulVec g+v)=
      (g j*g k-(if j=k then 1 else 0))*selectorWeight s α (M.mulVec g+(z+v))
    rw [supplementalHInputShift_selectorWeight]
    have he : (M.mulVec g+v)+z=M.mulVec g+(z+v) := by abel
    rw [he])

theorem proposition_H2_pair_matrix_rectangular {p r K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) (fun x => A.mulVec x) α x) ∂ν) ≤
      supplementalHPairPhysicalMatrixConstant C₀^(K+3)*s.bandwidth^2*κ/σ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  cases r with
  | zero =>
      have ht := hunit ⟨0,by omega⟩
      norm_num [vectorNormSq] at ht
  | succ n => exact proposition_H2_pair_matrix hp ν s A hC₀ hδ hκ hσ hunit hδh hc hδσ

/-- The actual shifted pair matrix estimate has no surface, entropy,
mean, trace or restoration supplier among its premises. -/
theorem proposition_H2_pair_matrix_shifted {p r K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (z : Vector p) {C₀ δ κ σ : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => z+A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) (fun x => z+A.mulVec x) α x) ∂ν) ≤
      supplementalHPairPhysicalMatrixConstant C₀^(K+3)*s.bandwidth^2*κ/σ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  have hR : Measurable (fun x : Vector r => z+A.mulVec x) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hrec : ∀ᵐ x ∂ν, z+A.mulVec x=z+A.mulVec (id x) := ae_of_all _ (fun _ => rfl)
  have hc0 := intrinsicRectangleConcentration_remove_ae_shift ν id measurable_id
    (fun x => z+A.mulVec x) hR A z hrec hc
  simp only [Measure.map_id] at hc0
  have h := proposition_H2_pair_matrix_rectangular (K := K) hp ν (supplementalHInputShift s z) A
    hC₀ hδ hκ hσ hunit hδh hc0 hδσ
  calc
    _ = (∫ x, ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
        symmetricNuclearNorm (selectorGaussianScore (supplementalHInputShift s z) (σ • A)
          (fun x => A.mulVec x) α x) ∂ν) := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      apply Finset.sum_congr rfl
      intro α _
      apply congrArg (fun M => supplementalHPairTupleAngle A α*symmetricNuclearNorm M)
      exact (supplementalHInputShift_pairScore s z (A.mulVec x) (σ • A) α).symm
    _ ≤ _ := h

end
end RectangleCLTArxivV1

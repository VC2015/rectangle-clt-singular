import RectangleCLTArxivV1.SubexponentialIntrinsicMain
import RectangleCLTArxivV1.TransfersProjection
import RectangleCLTCompanion.SplitV4.OrliczFaceTransfer

/-! The exact `K ↦ J K` sub-exponential branch of Corollary 3.
All logarithms are recomputed in the number of faces, and the width is the
actual expected maximum of the standardized Gaussian face projections. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem psi1Independent_projected_exact
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p m n : ℕ} {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : Psi1IndependentHypotheses μ X K) (M : Matrix (Fin m) (Fin p) ℝ)
    (J : ℝ) (hJ : 1 ≤ J) (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    Psi1IndependentHypotheses μ (fun i ω => M.mulVec (X i ω)) (J*K) := by
  have hY := subexponentialIndependent_projected (psi1_exponentialHypotheses_exact h) M J hJ hM
  refine ⟨hY.measurable,hY.independent,hY.centered,?_,hY.one_le_scale⟩
  intro i α
  let F : Ω → ℝ := fun ω => M.mulVec (X i ω) α
  have hs : J*K ∈ psi1Scales μ F :=
    ⟨zero_lt_one.trans_le hY.one_le_scale,hY.integrable_exp i α,hY.exponential_moment i α⟩
  exact (psi1Norm_le_iff (zero_le_one.trans hY.one_le_scale)).mpr
    ⟨⟨J*K,hs⟩,csInf_le (psi1Scales_bddBelow μ F) hs⟩

theorem orliczPolyhedralCLT_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m) (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) (K : ℝ)
    (h : Psi1IndependentHypotheses μ X K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 1 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J*σ α)
    (hvariance : ∀ α, dotProduct (ν α)
      ((covariance μ (normalizedObservationSum X)).mulVec (ν α)) = (σ α)^2) :
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤
      subexponentialWidthConstant * min 1
        (subexponentialWidthRate n m (J*K)
          (projectedGaussianMean A (standardizedFaceMap ν σ))) := by
  let M := standardizedFaceMap ν σ
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  let Y : Fin n → Ω → Vector m := fun i ω => M.mulVec (X i ω)
  have hY := subexponentialIndependent_projected (psi1_exponentialHypotheses_exact h) M J hJ hM
  have hcov : covariance μ (normalizedObservationSum Y) =
      M*covariance μ (normalizedObservationSum X)*M.transpose :=
    subexponential_projected_covariance (psi1_exponentialHypotheses_exact h) M
  have hunit : ∀ α, covariance μ (normalizedObservationSum Y) α α = 1 := by
    intro α
    rw [hcov]
    exact standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance α
  obtain ⟨C,hC⟩ := gaussian_factor_exists_of_psi1 (psi1Independent_projected_exact h M J hJ hM)
  have hgram : C*C.transpose = M*(A*A.transpose)*M.transpose := by
    simpa only [hA] using hC.trans hcov
  have hd := polyhedralDistance_le_standardizedRectangleDistance μ
    (normalizedObservationSum X) A C ν σ hσ hgram
  have hsum : normalizedObservationSum Y = fun ω => M.mulVec (normalizedObservationSum X ω) :=
    normalizedObservationSum_mulVec M X
  rw [←hsum] at hd
  have hc := subexponentialCLT_intrinsic μ hm hn Y hY hunit C hC
  rw [gaussianMaximumMean_projected M A C hgram] at hc
  exact hd.trans hc

end
end RectangleCLTArxivV1

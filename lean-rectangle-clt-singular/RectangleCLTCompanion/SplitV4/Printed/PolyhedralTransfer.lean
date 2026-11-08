import RectangleCLTCompanion.SplitV4.Printed.OrliczTransfer
import RectangleCLTCompanion.SplitV4.RelativeFaceTransfer
import RectangleCLTCompanion.SplitV4.PolynomialFaceTransfer

/-! The bounded-envelope and exact Orlicz branches of the printed
standardized-projection proof. The relative/polynomial branches and the
zero-variance deletion already have the same argument in the frozen source. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem psi1Norm_le_of_admissible_scale
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {K : ℝ}
    (hs : K ∈ psi1Scales μ X) : psi1Norm μ X ≤ ENNReal.ofReal K := by
  apply (psi1Norm_le_iff hs.1.le).mpr
  exact ⟨⟨K,hs⟩,csInf_le (psi1Scales_bddBelow μ X) hs⟩

/-- The exact psi1 triangle step at JK, without replacing K by2K.
Finite Jensen uses a leftover weight at zero and no coordinate independence. -/
theorem psi1_projected_at_exact_scale
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p m n : ℕ} {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : Psi1IndependentHypotheses μ X K) (M : Matrix (Fin m) (Fin p) ℝ)
    (J : ℝ) (hJ : 1 ≤ J) (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    Psi1IndependentHypotheses μ (fun i ω => M.mulVec (X i ω)) (J*K) := by
  have he := psi1_hypotheses_exponential_at_same_scale h
  have hY := subexponentialIndependent_projected he M J hJ hM
  refine ⟨hY.measurable,hY.independent,hY.centered,?_,hY.one_le_scale⟩
  intro i α
  exact psi1Norm_le_of_admissible_scale
    ⟨zero_lt_one.trans_le hY.one_le_scale,hY.integrable_exp i α,hY.exponential_moment i α⟩

theorem bounded_polyhedral_via_current_theorem
    {Ω : Type u} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m)
    (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 0 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J*σ α)
    (hvariance : ∀ α, dotProduct (ν α)
      ((covariance μ (sumVector ξ)).mulVec (ν α))=(σ α)^2) :
    polyhedralDistance μ (sumVector ξ) A ν ≤
      relativeUniversalConstant*min 1 (unrestrictedRate (J*δ) (dimensionLog m)) := by
  let M := standardizedFaceMap ν σ
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  let η : Fin n → Ω → Vector m := fun i ω => M.mulVec (ξ i ω)
  have hη : BoundedIndependentHypotheses μ η (J*δ) := boundedIndependent_projected h M J hJ hM
  have hcov : covariance μ (sumVector η)=M*covariance μ (sumVector ξ)*M.transpose :=
    covariance_projected_sum h M J hJ hM
  have hunit : ∀ α, covariance μ (sumVector η) α α=1 := by
    intro α
    rw [hcov]
    exact standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance α
  obtain ⟨C,hC⟩ := gaussian_factor_exists_of_boundedIndependent hη
  have hgram : C*C.transpose=M*(A*A.transpose)*M.transpose := by
    simpa only [hA] using hC.trans hcov
  have hd := polyhedralDistance_le_projected_rectangleDistance μ (sumVector ξ) A C ν σ hσ hgram
  have hsum : sumVector η=fun ω => M.mulVec (sumVector ξ ω) := funext (sumVector_mulVec M ξ)
  rw [← hsum] at hd
  exact hd.trans (relativeEnvelopeCLT μ hm η hη hunit C hC)

theorem orlicz_polyhedral_via_printed_transfer
    {Ω : Type u} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m) (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) (K : ℝ) (h : Psi1IndependentHypotheses μ X K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 1 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J*σ α)
    (hvariance : ∀ α, dotProduct (ν α)
      ((covariance μ (normalizedObservationSum X)).mulVec (ν α))=(σ α)^2) :
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤
      printedSubexponentialConstant*min 1
        (unrestrictedRate (subexponentialScale n (J*K)) (dimensionLog m)) := by
  let M := standardizedFaceMap ν σ
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  let Y : Fin n → Ω → Vector m := fun i ω => M.mulVec (X i ω)
  have he := psi1_hypotheses_exponential_at_same_scale h
  have hY := psi1_projected_at_exact_scale h M J hJ hM
  have hYe := psi1_hypotheses_exponential_at_same_scale hY
  have hcov : covariance μ (normalizedObservationSum Y)=
      M*covariance μ (normalizedObservationSum X)*M.transpose := subexponential_projected_covariance he M
  have hunit : ∀ α, covariance μ (normalizedObservationSum Y) α α=1 := by
    intro α
    rw [hcov]
    exact standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance α
  obtain ⟨C,hC⟩ := gaussian_factor_exists_of_subexponential hYe
  have hgram : C*C.transpose=M*(A*A.transpose)*M.transpose := by
    simpa only [hA] using hC.trans hcov
  have hd := polyhedralDistance_le_projected_rectangleDistance
    μ (normalizedObservationSum X) A C ν σ hσ hgram
  have hsum : normalizedObservationSum Y=fun ω => M.mulVec (normalizedObservationSum X ω) :=
    normalizedObservationSum_mulVec M X
  rw [← hsum] at hd
  apply hd.trans
  apply rectangleDistance_le
  intro R
  exact subexponential_via_printed_clipping μ m n hm hn Y (J*K) C hYe hunit hC R

end
end RectangleCLT.Companion.SplitV4.Printed

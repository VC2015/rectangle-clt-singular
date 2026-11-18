import RectangleCLTArxivV1.SupplementalGSeededSourceLaw

/-! The literal archived seeded fourth remainder is the scalar-kernel
combination of the three rank-dimensional actual copy patterns. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false

theorem cap_variableFourthPathIntegrandA_eq_rectangular_pattern
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t θ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hpos : 0 < t+ε) :
    s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t+ε) • C)) μ ξ x
      (thinningProbability t) (1+t) θ = capSeededFourthPattern s μ ξ A x ε t θ false false false := by
  rw [variableFourthPathIntegrandA_eq_seeded_product s μ ξ h C hC x ht ht1 hpos]
  rw [← seededFourthArrayExperiment_eq_product s μ ξ h C hC x ht ht1 hpos false false false]
  exact cap_seededFourthArrayExperiment_eq_rectangular_pattern s μ ξ h A C hA hC x ht ht1 hpos false false false

theorem cap_variableFourthPathIntegrandB_eq_rectangular_pattern
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t θ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hpos : 0 < t+ε) :
    s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t+ε) • C)) μ ξ x
      (thinningProbability t) (1+t) θ = capSeededFourthPattern s μ ξ A x ε t θ true true true := by
  rw [variableFourthPathIntegrandB_eq_seeded_product s μ ξ h C hC x ht ht1 hpos]
  rw [← seededFourthArrayExperiment_eq_product s μ ξ h C hC x ht ht1 hpos true true true]
  exact cap_seededFourthArrayExperiment_eq_rectangular_pattern s μ ξ h A C hA hC x ht ht1 hpos true true true

theorem cap_variableFourthPathIntegrandC_eq_rectangular_pattern
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t θ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hpos : 0 < t+ε) :
    s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t+ε) • C)) μ ξ x
      (thinningProbability t) (1+t) θ = capSeededFourthPattern s μ ξ A x ε t θ false true true := by
  rw [variableFourthPathIntegrandC_eq_seeded_product s μ ξ h C hC x ht ht1 hpos]
  rw [← seededFourthArrayExperiment_eq_product s μ ξ h C hC x ht ht1 hpos false true true]
  exact cap_seededFourthArrayExperiment_eq_rectangular_pattern s μ ξ h A C hA hC x ht ht1 hpos false true true

/-- Exact connection to the original seededFourthRemainder definition. -/
theorem cap_seededFourthRemainder_eq_patterns
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hpos : 0 < t+ε) :
    seededFourthRemainder s μ ξ C x ε t =
      (∫ θ in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*
        capSeededFourthPattern s μ ξ A x ε t θ false false false)+
      (1-t)/2*(∫ θ in (0 : ℝ)..1, (1-θ)*capSeededFourthPattern s μ ξ A x ε t θ true true true)+
      (t*(1-t)/(3*(1+t)))*(∫ θ in (0 : ℝ)..1, capSeededFourthPattern s μ ξ A x ε t θ false true true) := by
  unfold seededFourthRemainder
  simp_rw [cap_variableFourthPathIntegrandA_eq_rectangular_pattern s μ ξ h A C hA hC x ht ht1 hpos,
    cap_variableFourthPathIntegrandB_eq_rectangular_pattern s μ ξ h A C hA hC x ht ht1 hpos,
    cap_variableFourthPathIntegrandC_eq_rectangular_pattern s μ ξ h A C hA hC x ht ht1 hpos]

end
end RectangleCLTArxivV1

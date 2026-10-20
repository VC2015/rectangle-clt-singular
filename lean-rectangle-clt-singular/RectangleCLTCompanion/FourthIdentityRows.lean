import RectangleCLTCompanion.FourthIdentityTaylor

/-! Exact row-wise fourth-order kernels. These are actual nested integrals of
checked fourth derivatives. The outer expectation form keeps fresh row laws
explicit; Fubini can subsequently put the interpolation parameter outside. -/

open MeasureTheory
open scoped BigOperators Interval

set_option maxHeartbeats 800000

namespace RectangleCLT.Companion

noncomputable def fourthKernel (t r : ℝ) : ℝ :=
  (1 + t) / 6 * (1 - r) ^ 2 * ((3 - t) * r - 2 * t)

theorem fourthKernel_eq (t r : ℝ) (ht : 0 ≤ t) :
    fourthKernel t r =
      ((t - 3) / (1 + t) ^ 3) * ((1 + t) ^ 4 / 6 * (1 - r) ^ 3) +
        thinningProbability t * ((1 + t) ^ 3 / 2 * (1 - r) ^ 2) := by
  unfold fourthKernel thinningProbability
  have hn : 1 + t ≠ 0 := by linarith
  field_simp [hn]
  ring

end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

/-- The genuine repeated-row fourth-order term in the Bernoulli derivative. -/
def fourthRowA {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  ∫ ω, (∫ r in (0 : ℝ)..1, Companion.fourthKernel t r *
    s.convolutionTranslationD4 ν (line x (ξ ω) (thinningScale t * r)) (ξ ω)) ∂μ

private theorem row_remainders_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) (a : ℝ) :
    Integrable (fun ω => s.convolution ν (line x (ξ ω) a) -
      s.convolutionTaylor3 ν x (a • ξ ω)) μ ∧
    Integrable (fun ω => s.convolutionTranslationD1 ν (line x (ξ ω) a) (ξ ω) -
      s.convolutionGradientTaylor2 ν x (ξ ω) a) μ := by
  have hline : Measurable (fun ω => line x (ξ ω) a) := by
    change Measurable (fun ω => x + a • ξ ω)
    exact measurable_const.add (measurable_const.smul hξ)
  have hiA0 : Integrable (fun ω => s.convolution ν (line x (ξ ω) a)) μ :=
    (integrable_const (1 : ℝ)).mono'
      (((s.continuous_convolution ν).measurable.comp hline).aestronglyMeasurable)
      (ae_of_all μ (fun ω => s.norm_convolution_le_one ν _))
  have hiD1 := s.integrable_convolutionTranslationD1_observation ν μ ξ hξ hbound x
  have hiD2 := s.integrable_convolutionTranslationD2_observation ν μ ξ hξ hbound x
  have hiD3 := s.integrable_convolutionTranslationD3_observation ν μ ξ hξ hbound x
  have hiB0 : Integrable (fun ω => s.convolutionTaylor3 ν x (a • ξ ω)) μ := by
    simp_rw [convolutionTaylor3, s.convolutionTranslationD1_smul,
      s.convolutionTranslationD2_smul, s.convolutionTranslationD3_smul]
    exact (((integrable_const _).add (hiD1.const_mul a)).add
      ((hiD2.const_mul (a ^ 2)).div_const 2)).add ((hiD3.const_mul (a ^ 3)).div_const 6)
  have hiB1 : Integrable (fun ω => s.convolutionGradientTaylor2 ν x (ξ ω) a) μ :=
    (hiD1.add (hiD2.const_mul a)).add ((hiD3.const_mul (a ^ 2)).div_const 2)
  have hiA1 : Integrable (fun ω => s.convolutionTranslationD1 ν (line x (ξ ω) a) (ξ ω)) μ := by
    unfold convolutionTranslationD1
    apply integrable_finset_sum
    intro j _
    apply (integrable_const (δ * (1 / s.bandwidth))).mono'
    · exact (((s.continuous_convolutionFirstDerivative ν j).measurable.comp hline).mul
        ((measurable_pi_apply j).comp hξ)).aestronglyMeasurable
    · filter_upwards [hbound] with ω hω
      rw [norm_mul, Real.norm_eq_abs]
      have hh := mul_le_mul (s.norm_convolutionFirstDerivative_le ν (line x (ξ ω) a) j)
        ((norm_le_pi_norm (ξ ω) j).trans hω) (norm_nonneg (ξ ω j))
        (div_pos (by norm_num) s.bandwidth_pos).le
      simpa only [mul_comm, Real.norm_eq_abs] using hh
  exact ⟨hiA0.sub hiB0, hiA1.sub hiB1⟩

theorem oneObservationTaylorResidual_eq_fourthRowA
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.oneObservationTaylorResidual ν μ ξ x t = s.fourthRowA ν μ ξ x t := by
  let a := thinningScale t
  let R₀ := fun ω => s.convolution ν (line x (ξ ω) a) -
    s.convolutionTaylor3 ν x (a • ξ ω)
  let R₁ := fun ω => s.convolutionTranslationD1 ν (line x (ξ ω) a) (ξ ω) -
    s.convolutionGradientTaylor2 ν x (ξ ω) a
  have hi := s.row_remainders_integrable ν μ ξ hξ hbound x a
  have hline : Measurable (fun ω => line x (ξ ω) a) := by
    change Measurable (fun ω => x + a • ξ ω)
    exact measurable_const.add (measurable_const.smul hξ)
  have e₀ : s.translatedConvolution ν μ ξ x a - s.convolution ν x -
      a ^ 2 / 2 * s.observationSecondTerm ν μ ξ x -
      a ^ 3 / 6 * s.observationThirdTerm ν μ ξ x = ∫ ω, R₀ ω ∂μ := by
    have hiA0 : Integrable (fun ω => s.convolution ν (line x (ξ ω) a)) μ :=
      (integrable_const (1 : ℝ)).mono'
        (((s.continuous_convolution ν).measurable.comp
          hline).aestronglyMeasurable)
        (ae_of_all μ (fun ω => s.norm_convolution_le_one ν _))
    have hiB0 := hiA0.sub hi.1
    have hiB0' : Integrable (fun ω => s.convolutionTaylor3 ν x (a • ξ ω)) μ := by
      convert hiB0 using 1
      ext ω
      dsimp
      ring
    change _ = ∫ ω, s.convolution ν (line x (ξ ω) a) - s.convolutionTaylor3 ν x (a • ξ ω) ∂μ
    rw [integral_sub hiA0 hiB0']
    rw [s.integral_convolutionTaylor3_centered ν μ ξ hξ hbound hcenter x a]
    unfold translatedConvolution observationSecondTerm observationThirdTerm
    ring
  have e₁ : (∫ ω, ∑ j, ξ ω j * s.convolutionFirstDerivative ν (line x (ξ ω) a) j ∂μ) -
      a * s.observationSecondTerm ν μ ξ x - a ^ 2 / 2 * s.observationThirdTerm ν μ ξ x =
        ∫ ω, R₁ ω ∂μ := by
    have hiB1 : Integrable (fun ω => s.convolutionGradientTaylor2 ν x (ξ ω) a) μ :=
      ((s.integrable_convolutionTranslationD1_observation ν μ ξ hξ hbound x).add
        ((s.integrable_convolutionTranslationD2_observation ν μ ξ hξ hbound x).const_mul a)).add
        (((s.integrable_convolutionTranslationD3_observation ν μ ξ hξ hbound x).const_mul (a ^ 2)).div_const 2)
    have hiA1 := hi.2.add hiB1
    have hiA1' : Integrable (fun ω => s.convolutionTranslationD1 ν (line x (ξ ω) a) (ξ ω)) μ := by
      convert hiA1 using 1
      ext ω
      dsimp
      ring
    change _ = ∫ ω, s.convolutionTranslationD1 ν (line x (ξ ω) a) (ξ ω) - s.convolutionGradientTaylor2 ν x (ξ ω) a ∂μ
    rw [integral_sub hiA1' hiB1]
    rw [s.integral_convolutionGradientTaylor2_centered ν μ ξ hξ hbound hcenter x a]
    unfold observationSecondTerm observationThirdTerm convolutionTranslationD1
    simp only [mul_comm (ξ _ _)]
    ring
  unfold oneObservationTaylorResidual
  rw [e₀, e₁]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi.1.const_mul _) (hi.2.const_mul _)]
  change _ = ∫ ω, (∫ r in (0 : ℝ)..1, Companion.fourthKernel t r *
    s.convolutionTranslationD4 ν (line x (ξ ω) (thinningScale t * r)) (ξ ω)) ∂μ
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  dsimp [R₀, R₁]
  change ((t - 3) / (1 + t) ^ 3) *
    (s.convolution ν (x + a • ξ ω) - s.convolutionTaylor3 ν x (a • ξ ω)) +
    thinningProbability t * (s.convolutionTranslationD1 ν (x + a • ξ ω) (ξ ω) -
    s.convolutionGradientTaylor2 ν x (ξ ω) a) = _
  rw [s.convolutionTaylor3_integral_remainder, s.convolutionGradientTaylor2_integral_remainder]
  have hc : Continuous (fun r => s.convolutionTranslationD4 ν (line x (ξ ω) (a * r)) (ξ ω)) :=
    (s.continuous_convolutionTranslationD4 ν (ξ ω)).comp
      (continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const))
  have hi₀ : IntervalIntegrable (fun r => (a ^ 4 / 6) * (1 - r) ^ 3 *
      s.convolutionTranslationD4 ν (line x (ξ ω) (a * r)) (ξ ω)) volume 0 1 :=
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).mul hc).intervalIntegrable 0 1
  have hi₁ : IntervalIntegrable (fun r => (a ^ 3 / 2) * (1 - r) ^ 2 *
      s.convolutionTranslationD4 ν (line x (ξ ω) (a * r)) (ξ ω)) volume 0 1 :=
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).mul hc).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hi₀.const_mul _) (hi₁.const_mul _)]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp [fourthRowA]
  rw [Companion.fourthKernel_eq t r ht]
  dsimp [a, thinningScale]
  ring

end
end RectangleCLT.FaceSmoother

import RectangleCLTCompanion.SplitV4.VariableAmplitudeInterpolation

/-! Exact one-observation Taylor expansion for the general-amplitude
interpolation. Every remainder below is an actual integrable expectation. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.FaceSmoother
noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

def variableRowTaylorRemainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (a c b : ℝ) : ℝ :=
  ∫ ω, c*(s.convolution ν (x+a • T ω)-s.convolutionTaylor3 ν x (a • T ω)) +
    b*(s.convolutionTranslationD1 ν (x+a • T ω) (T ω)-
      s.convolutionGradientTaylor2 ν x (T ω) a) ∂μ

def variableFourthRowA {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (a c b : ℝ) : ℝ :=
  ∫ ω, (∫ r in (0 : ℝ)..1,
    (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*
      s.convolutionTranslationD4 ν (line x (T ω) (a*r)) (T ω)) ∂μ

theorem integrable_variableRowTaylor_remainders
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (x : Vector p) (a : ℝ) :
    Integrable (fun ω => s.convolution ν (x+a • T ω)-s.convolutionTaylor3 ν x (a • T ω)) μ ∧
      Integrable (fun ω => s.convolutionTranslationD1 ν (x+a • T ω) (T ω)-
        s.convolutionGradientTaylor2 ν x (T ω) a) μ := by
  have hline : Measurable (fun ω => x+a • T ω) := measurable_const.add (measurable_const.smul hT)
  have h0 := integrable_bounded_test_comp μ _ hline _ (s.continuous_convolution ν)
    1 (fun y => s.norm_convolution_le_one ν y)
  have h1 := s.integrable_convolutionTranslationD1_observation ν μ T hT hbound x
  have h2 := s.integrable_convolutionTranslationD2_observation ν μ T hT hbound x
  have h3 := s.integrable_convolutionTranslationD3_observation ν μ T hT hbound x
  have hp0 : Integrable (fun ω => s.convolutionTaylor3 ν x (a • T ω)) μ := by
    simp_rw [convolutionTaylor3, s.convolutionTranslationD1_smul,
      s.convolutionTranslationD2_smul, s.convolutionTranslationD3_smul]
    exact (((integrable_const _).add (h1.const_mul a)).add
      ((h2.const_mul (a^2)).div_const 2)).add ((h3.const_mul (a^3)).div_const 6)
  have hp1 : Integrable (fun ω => s.convolutionGradientTaylor2 ν x (T ω) a) μ :=
    (h1.add (h2.const_mul a)).add ((h3.const_mul (a^2)).div_const 2)
  have hD1 : Integrable (fun ω => s.convolutionTranslationD1 ν (x+a • T ω) (T ω)) μ := by
    unfold convolutionTranslationD1
    apply integrable_finset_sum
    intro j _
    apply (integrable_const (δ*(1/s.bandwidth))).mono'
    · exact (((s.continuous_convolutionFirstDerivative ν j).measurable.comp hline).mul
        ((measurable_pi_apply j).comp hT)).aestronglyMeasurable
    · filter_upwards [hbound] with ω hω
      rw [norm_mul, Real.norm_eq_abs]
      have hh := mul_le_mul (s.norm_convolutionFirstDerivative_le ν (x+a • T ω) j)
        ((norm_le_pi_norm (T ω) j).trans hω) (norm_nonneg (T ω j))
        (div_pos (by norm_num) s.bandwidth_pos).le
      simpa only [mul_comm, Real.norm_eq_abs] using hh
  exact ⟨h0.sub hp0, hD1.sub hp1⟩

theorem variableRowTaylorRemainder_eq_fourthRowA
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → Vector p)
    (x : Vector p) (a c b : ℝ) :
    s.variableRowTaylorRemainder ν μ T x a c b = s.variableFourthRowA ν μ T x a c b := by
  unfold variableRowTaylorRemainder variableFourthRowA
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  change c*(s.convolution ν (x+a • T ω)-s.convolutionTaylor3 ν x (a • T ω)) +
    b*(s.convolutionTranslationD1 ν (x+a • T ω) (T ω)-s.convolutionGradientTaylor2 ν x (T ω) a) = _
  rw [s.convolutionTaylor3_integral_remainder, s.convolutionGradientTaylor2_integral_remainder]
  have hi0 : IntervalIntegrable (fun r : ℝ => a^4/6*(1-r)^3*
      s.convolutionTranslationD4 ν (line x (T ω) (a*r)) (T ω)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul
    · fun_prop
    · exact (s.continuous_convolutionTranslationD4 ν (T ω)).comp (by unfold line; fun_prop)
  have hi1 : IntervalIntegrable (fun r : ℝ => a^3/2*(1-r)^2*
      s.convolutionTranslationD4 ν (line x (T ω) (a*r)) (T ω)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul
    · fun_prop
    · exact (s.continuous_convolutionTranslationD4 ν (T ω)).comp (by unfold line; fun_prop)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hi0.const_mul c) (hi1.const_mul b)]
  apply intervalIntegral.integral_congr
  intro r _
  ring

theorem variableRowTranslation_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, T ω j ∂μ) = 0)
    (x : Vector p) (a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ))
    (h3 : c*a^3/6+b*a^2/2 = d) :
    c*(s.translatedConvolution ν μ T x a-s.convolution ν x) +
      b*(∫ ω, ∑ j, T ω j*s.convolutionFirstDerivative ν (x+a • T ω) j ∂μ) =
      -(1/2 : ℝ)*s.observationSecondTerm ν μ T x +
        d*s.observationThirdTerm ν μ T x + s.variableFourthRowA ν μ T x a c b := by
  have hi := s.integrable_variableRowTaylor_remainders ν μ T hT hbound x a
  have hline : Measurable (fun ω => x+a • T ω) := measurable_const.add (measurable_const.smul hT)
  have h0 := integrable_bounded_test_comp μ _ hline _ (s.continuous_convolution ν)
    1 (fun y => s.norm_convolution_le_one ν y)
  have hp0 : Integrable (fun ω => s.convolutionTaylor3 ν x (a • T ω)) μ := by
    convert h0.sub hi.1 using 1
    ext ω
    simp only [Pi.sub_apply]
    ring
  have hp1 : Integrable (fun ω => s.convolutionGradientTaylor2 ν x (T ω) a) μ :=
    ((s.integrable_convolutionTranslationD1_observation ν μ T hT hbound x).add
      ((s.integrable_convolutionTranslationD2_observation ν μ T hT hbound x).const_mul a)).add
        (((s.integrable_convolutionTranslationD3_observation ν μ T hT hbound x).const_mul (a^2)).div_const 2)
  have hD1 : Integrable (fun ω => s.convolutionTranslationD1 ν (x+a • T ω) (T ω)) μ := by
    convert hi.2.add hp1 using 1
    ext ω
    simp only [Pi.add_apply]
    ring
  have e0 : (∫ ω, s.convolution ν (x+a • T ω)-s.convolutionTaylor3 ν x (a • T ω) ∂μ) =
      s.translatedConvolution ν μ T x a-s.convolution ν x-
        a^2/2*s.observationSecondTerm ν μ T x-a^3/6*s.observationThirdTerm ν μ T x := by
    rw [integral_sub h0 hp0, s.integral_convolutionTaylor3_centered ν μ T hT hbound hcenter x a]
    unfold translatedConvolution observationSecondTerm observationThirdTerm
    change (∫ ω, s.convolution ν (line x (T ω) a) ∂μ) - _ = _
    ring
  have e1 : (∫ ω, s.convolutionTranslationD1 ν (x+a • T ω) (T ω)-
        s.convolutionGradientTaylor2 ν x (T ω) a ∂μ) =
      (∫ ω, ∑ j, T ω j*s.convolutionFirstDerivative ν (x+a • T ω) j ∂μ)-
        a*s.observationSecondTerm ν μ T x-a^2/2*s.observationThirdTerm ν μ T x := by
    rw [integral_sub hD1 hp1,
      s.integral_convolutionGradientTaylor2_centered ν μ T hT hbound hcenter x a]
    unfold convolutionTranslationD1
    simp only [mul_comm]
    unfold observationSecondTerm observationThirdTerm
    ring
  rw [← s.variableRowTaylorRemainder_eq_fourthRowA ν μ T x a c b]
  unfold variableRowTaylorRemainder
  rw [integral_add (hi.1.const_mul c) (hi.2.const_mul b), integral_const_mul, integral_const_mul, e0, e1]
  linear_combination (s.observationSecondTerm ν μ T x)*h2 + (s.observationThirdTerm ν μ T x)*h3

end
end RectangleCLT.FaceSmoother

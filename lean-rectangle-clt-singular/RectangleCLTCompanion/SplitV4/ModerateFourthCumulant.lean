import RectangleCLTCompanion.SplitV4.ModerateTiltBounds

/-! The actual fourth tilted cumulant, with its variance-weighted bound. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {δ : ℝ}

theorem moderate_integral_centered_fourth (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (c : ℝ) :
    (∫ ω, (X ω - c) ^ 4 ∂μ) =
      (∫ ω, X ω ^ 4 ∂μ) - 4 * c * (∫ ω, X ω ^ 3 ∂μ) +
      6 * c ^ 2 * (∫ ω, X ω ^ 2 ∂μ) - 4 * c ^ 3 * (∫ ω, X ω ∂μ) + c ^ 4 := by
  have hi := moderate_integrable_bounded hX hbound
  have h2 := moderate_integrable_pow hX hδ hbound 2
  have h3 := moderate_integrable_pow hX hδ hbound 3
  have h4 := moderate_integrable_pow hX hδ hbound 4
  calc
    _ = ∫ ω, ((X ω ^ 4 - (4 * c) * X ω ^ 3) + (6 * c ^ 2) * X ω ^ 2) -
        (4 * c ^ 3) * X ω + c ^ 4 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by ring)
    _ = _ := by
      rw [moderate_integral_add (fun ω => ((X ω ^ 4 - (4 * c) * X ω ^ 3) + (6 * c ^ 2) * X ω ^ 2) - (4 * c ^ 3) * X ω)
          (fun _ => c ^ 4) (((h4.sub (h3.const_mul _)).add (h2.const_mul _)).sub (hi.const_mul _)) (integrable_const _),
        moderate_integral_sub (fun ω => (X ω ^ 4 - (4 * c) * X ω ^ 3) + (6 * c ^ 2) * X ω ^ 2)
          (fun ω => (4 * c ^ 3) * X ω) ((h4.sub (h3.const_mul _)).add (h2.const_mul _)) (hi.const_mul _),
        moderate_integral_add (fun ω => X ω ^ 4 - (4 * c) * X ω ^ 3)
          (fun ω => (6 * c ^ 2) * X ω ^ 2) (h4.sub (h3.const_mul _)) (h2.const_mul _),
        moderate_integral_sub (fun ω => X ω ^ 4) (fun ω => (4 * c) * X ω ^ 3) h4 (h3.const_mul _)]
      simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul]

theorem moderateTiltFourthCumulant_eq_integral (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    moderateTiltFourthCumulant μ X t =
      (∫ ω, (X ω - moderateTiltMean μ X t) ^ 4 ∂moderateScalarTilt μ X t) -
        3 * moderateTiltVariance μ X t ^ 2 := by
  letI := moderateScalarTilt_probability hX hbound t
  rw [moderate_integral_centered_fourth hX hδ (moderateScalarTilt_bound hbound t)]
  simp_rw [← moderateTiltMoment_eq_integral]
  have hm := moderateTiltMean_eq_integral (μ := μ) (X := X) t
  rw [← hm]
  unfold moderateTiltFourthCumulant moderateTiltVariance
  ring

theorem moderateTiltVariance_nonneg (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) : 0 ≤ moderateTiltVariance μ X t := by
  rw [moderateTiltVariance_eq_variance hX hbound t]
  exact variance_nonneg _ _

theorem moderateTiltVariance_le_sq (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) : moderateTiltVariance μ X t ≤ δ ^ 2 := by
  letI := moderateScalarTilt_probability hX hbound t
  have hb := moderateScalarTilt_bound hbound t
  rw [moderateTiltVariance_eq_variance hX hbound t]
  apply (variance_le_expectation_sq hX.aestronglyMeasurable).trans
  have hh := integral_mono_ae (moderate_integrable_pow hX hδ hb 2) (integrable_const (δ ^ 2))
    (hb.mono (fun ω hω => by dsimp only; nlinarith [sq_nonneg (X ω), abs_le.mp hω]))
  simpa only [integral_const, measureReal_univ_eq_one, one_smul, Pi.pow_apply] using hh

theorem moderateTilt_centered_fourth_le (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    (∫ ω, (X ω - moderateTiltMean μ X t) ^ 4 ∂moderateScalarTilt μ X t) ≤
      4 * δ ^ 2 * moderateTiltVariance μ X t := by
  letI := moderateScalarTilt_probability hX hbound t
  have hc := moderateTilt_centered_bound hX hbound t
  have hi := moderate_integrable_shift_pow hX hδ (moderateScalarTilt_bound hbound t) (moderateTiltMean μ X t)
  have heq : (∫ ω, (X ω - moderateTiltMean μ X t) ^ 2 ∂moderateScalarTilt μ X t) =
      moderateTiltVariance μ X t := by
    rw [moderateTiltVariance_eq_variance hX hbound t, variance_eq_integral hX.aemeasurable,
      ← moderateTiltMean_eq_integral]
  rw [← heq, ← integral_const_mul]
  apply integral_mono_ae (hi 4) ((hi 2).const_mul _)
  filter_upwards [hc] with ω hω
  change (X ω - moderateTiltMean μ X t) ^ 4 ≤ 4 * δ ^ 2 * (X ω - moderateTiltMean μ X t) ^ 2
  have hh : (X ω - moderateTiltMean μ X t) ^ 2 ≤ 4 * δ ^ 2 := by
    have ha := abs_le.mp hω
    nlinarith [sq_nonneg (|X ω - moderateTiltMean μ X t| - 2 * δ)]
  nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (X ω - moderateTiltMean μ X t))]

theorem moderateTiltFourthCumulant_abs_le (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    |moderateTiltFourthCumulant μ X t| ≤ 7 * δ ^ 2 * moderateTiltVariance μ X t := by
  have hv0 := moderateTiltVariance_nonneg hX hbound t
  have hv := moderateTiltVariance_le_sq hX hδ hbound t
  have h4 := moderateTilt_centered_fourth_le hX hδ hbound t
  have h40 : 0 ≤ ∫ ω, (X ω - moderateTiltMean μ X t) ^ 4 ∂moderateScalarTilt μ X t :=
    integral_nonneg (fun ω => by positivity)
  rw [moderateTiltFourthCumulant_eq_integral hX hδ hbound t]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg h40, abs_of_nonneg (by positivity : 0 ≤ 3 * moderateTiltVariance μ X t ^ 2)]
  have hsq := mul_le_mul_of_nonneg_right hv hv0
  nlinarith

end
end RectangleCLT.Companion.SplitV4

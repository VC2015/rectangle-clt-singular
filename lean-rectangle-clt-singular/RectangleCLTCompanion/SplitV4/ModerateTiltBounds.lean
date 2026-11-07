import RectangleCLTCompanion.SplitV4.ModerateCumulants

/-! Actual Esscher density and variance bounds for arbitrary bounded laws. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {δ : ℝ}

theorem moderate_integral_add (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ ω, f ω + g ω ∂μ) = (∫ ω, f ω ∂μ) + (∫ ω, g ω ∂μ) := integral_add hf hg

theorem moderate_integral_sub (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ ω, f ω - g ω ∂μ) = (∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ) := integral_sub hf hg

theorem moderate_exponent_bounds (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    ∀ᵐ ω ∂μ, -(|t| * δ) ≤ t * X ω ∧ t * X ω ≤ |t| * δ := by
  filter_upwards [hbound] with ω hω
  have hh : |t * X ω| ≤ |t| * δ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  exact abs_le.mp hh

theorem moderate_mgf_bounds (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    Real.exp (- (|t| * δ)) ≤ mgf X μ t ∧ mgf X μ t ≤ Real.exp (|t| * δ) := by
  have hi := moderate_integrable_exp hX hbound t
  constructor
  · have hh := integral_mono_ae (integrable_const (Real.exp (- (|t| * δ)))) hi
      ((moderate_exponent_bounds hbound t).mono fun ω hω => Real.exp_le_exp.mpr hω.1)
    simpa only [integral_const, measureReal_univ_eq_one, one_smul, mgf] using hh
  · have hh := integral_mono_ae hi (integrable_const (Real.exp (|t| * δ)))
      ((moderate_exponent_bounds hbound t).mono fun ω hω => Real.exp_le_exp.mpr hω.2)
    simpa only [integral_const, measureReal_univ_eq_one, one_smul, mgf] using hh

theorem moderateTilt_density_bounds (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    ∀ᵐ ω ∂μ, Real.exp (-2 * |t| * δ) ≤ Real.exp (t * X ω) / mgf X μ t ∧
      Real.exp (t * X ω) / mgf X μ t ≤ Real.exp (2 * |t| * δ) := by
  have hM := moderate_mgf_bounds hX hbound t
  have hp := mgf_pos (moderate_integrable_exp hX hbound t)
  filter_upwards [moderate_exponent_bounds hbound t] with ω hω
  constructor
  · apply (le_div_iff₀ hp).mpr
    calc
      _ ≤ Real.exp (-2 * |t| * δ) * Real.exp (|t| * δ) :=
        mul_le_mul_of_nonneg_left hM.2 (Real.exp_pos _).le
      _ = Real.exp (- (|t| * δ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hω.1
  · apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ Real.exp (|t| * δ) := Real.exp_le_exp.mpr hω.2
      _ = Real.exp (2 * |t| * δ) * Real.exp (- (|t| * δ)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM.1 (Real.exp_pos _).le

theorem moderateTilt_integral_nonneg_bounds (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) {f : Ω → ℝ}
    (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    Real.exp (-2 * |t| * δ) * (∫ ω, f ω ∂μ) ≤ ∫ ω, f ω ∂moderateScalarTilt μ X t ∧
      (∫ ω, f ω ∂moderateScalarTilt μ X t) ≤ Real.exp (2 * |t| * δ) * (∫ ω, f ω ∂μ) := by
  have hm : Measurable (fun ω => Real.exp (t * X ω) / mgf X μ t) :=
    ((measurable_const.mul hX).exp.div_const (mgf X μ t))
  have hi : Integrable (fun ω => Real.exp (t * X ω) / mgf X μ t * f ω) μ := by
    apply (hf.const_mul (Real.exp (2 * |t| * δ))).mono'
      (hm.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    filter_upwards [hf0, moderateTilt_density_bounds hX hbound t] with ω hω hρ
    change 0 ≤ f ω at hω
    change ‖Real.exp (t * X ω) / mgf X μ t * f ω‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      ((Real.exp_pos (-2 * |t| * δ)).le.trans hρ.1) hω)]
    exact mul_le_mul_of_nonneg_right hρ.2 hω
  rw [moderateScalarTilt, integral_tilted_mul_eq_mgf]
  simp only [smul_eq_mul]
  constructor
  · rw [← integral_const_mul]
    apply integral_mono_ae (hf.const_mul _) hi
    filter_upwards [hf0, moderateTilt_density_bounds hX hbound t] with ω hω hρ
    exact mul_le_mul_of_nonneg_right hρ.1 hω
  · rw [← integral_const_mul]
    apply integral_mono_ae hi (hf.const_mul _)
    filter_upwards [hf0, moderateTilt_density_bounds hX hbound t] with ω hω hρ
    exact mul_le_mul_of_nonneg_right hρ.2 hω


theorem moderate_integrable_shift_pow (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (c : ℝ) (k : ℕ) :
    Integrable (fun ω => (X ω - c) ^ k) μ := by
  apply moderate_integrable_pow (hX.sub_const c) (add_nonneg hδ (abs_nonneg c))
  filter_upwards [hbound] with ω hω
  exact (abs_sub _ _).trans (add_le_add_right hω _)

theorem moderate_integral_shift_sq (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (c : ℝ) :
    (∫ ω, (X ω - c) ^ 2 ∂μ) = variance X μ + ((∫ ω, X ω ∂μ) - c) ^ 2 := by
  have hi := moderate_integrable_bounded hX hbound
  have hp := moderate_integrable_pow hX hδ hbound 2
  calc
    _ = ∫ ω, (X ω ^ 2 - 2 * c * X ω) + c ^ 2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by ring)
    _ = _ := by
      rw [moderate_integral_add (fun ω => X ω ^ 2 - 2 * c * X ω) (fun _ => c ^ 2)
          (hp.sub (hi.const_mul _)) (integrable_const _),
        moderate_integral_sub (fun ω => X ω ^ 2) (fun ω => 2 * c * X ω) hp (hi.const_mul _), integral_const_mul, integral_const,
        measureReal_univ_eq_one, one_smul, variance_def' (moderate_memLp_two hX hbound)]
      change _ = (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 + _
      ring

theorem moderate_variance_le_shift_sq (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (c : ℝ) :
    variance X μ ≤ ∫ ω, (X ω - c) ^ 2 ∂μ := by
  rw [moderate_integral_shift_sq hX hδ hbound c]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- These bounds are stronger than the independent-copy `exp(±4δ|t|)`
bounds needed in the paper. They use the minimizing property of variance. -/
theorem moderateTiltVariance_exp_bounds (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    Real.exp (-2 * |t| * δ) * variance X μ ≤ moderateTiltVariance μ X t ∧
      moderateTiltVariance μ X t ≤ Real.exp (2 * |t| * δ) * variance X μ := by
  letI := moderateScalarTilt_probability hX hbound t
  have hb := moderateScalarTilt_bound hbound t
  have hactual := moderateTiltVariance_eq_variance hX hbound t
  have horig := variance_eq_integral hX.aemeasurable (μ := μ)
  have htilt := variance_eq_integral hX.aemeasurable (μ := moderateScalarTilt μ X t)
  constructor
  · have hlow := (moderateTilt_integral_nonneg_bounds hX hbound t
      (moderate_integrable_shift_pow hX hδ hbound (∫ ω, X ω ∂moderateScalarTilt μ X t) 2)
      (ae_of_all _ (fun ω => sq_nonneg _))).1
    have hm := mul_le_mul_of_nonneg_left
      (moderate_variance_le_shift_sq hX hδ hbound (∫ ω, X ω ∂moderateScalarTilt μ X t))
      (Real.exp_pos (-2 * |t| * δ)).le
    rw [hactual, htilt]
    exact hm.trans hlow
  · have hupp := (moderateTilt_integral_nonneg_bounds hX hbound t
      (moderate_integrable_shift_pow hX hδ hbound (∫ ω, X ω ∂μ) 2)
      (ae_of_all _ (fun ω => sq_nonneg _))).2
    have hm := moderate_variance_le_shift_sq (μ := moderateScalarTilt μ X t) hX hδ hb (∫ ω, X ω ∂μ)
    rw [hactual]
    exact hm.trans (hupp.trans_eq (by rw [← horig]))

end
end RectangleCLT.Companion.SplitV4

import RectangleCLTArxivV1.LowerUnmaskedProfile
import RectangleCLTArxivV1.LowerWidthVarianceBudget

/-! The small prescribed raw scale verifies every parameter and width
condition for the explicitly constructed unmasked sequence. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerUnmasked_count_identity {n : ℕ} {ell : ℝ} (hn : 1 ≤ n) :
    (n : ℝ)*(ell/(2*n)) = ell/2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

theorem tendsto_lowerUnmasked_raw_variance {a : ℕ → ℝ} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (Real.log (m n : ℝ)/(2*n))*(a n)^2) atTop (𝓝 0) := by
  obtain ⟨c,hc,hg⟩ := exists_absoluteGaussianMean_sqrt_lower
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hbound : Tendsto (fun n : ℕ => (lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n)^2/(2*c^2)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0),zero_div] using (hsmall.pow 2).div_const (2*c^2)
  apply squeeze_zero' _ _ hbound
  · exact Eventually.of_forall (fun n => mul_nonneg
      (div_nonneg (Real.log_nonneg (by exact_mod_cast (by have := hm n; omega : 1 ≤ m n))) (by positivity))
      (sq_nonneg _))
  · filter_upwards [hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with n hnL hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact lowerWidthBudget_variance hnL hn0 (log_exp_mul_nat_ge_one (hr n)) hc
      (hg (r n) (hr n)) (lowerUnmasked_count_identity hn)

theorem eventually_lowerUnmaskedSequence_fields {a : ℕ → ℝ} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (lowerUnmaskedSequence a m n).theta = Real.log (m n : ℝ)/(2*n) ∧
      (lowerUnmaskedSequence a m n).amplitude = a n ∧
      (lowerUnmaskedSequence a m n).variance = (Real.log (m n : ℝ)/(2*n))*(a n)^2 := by
  have hv := (tendsto_lowerUnmasked_raw_variance hr hm hmTop hsmall).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [ha,hv,eventually_ge_atTop 1] with n hna hnv hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ : 0 < Real.log (m n : ℝ)/(2*n) :=
    div_pos (Real.log_pos (by exact_mod_cast hm n)) (by positivity)
  have ht := lowerUnmaskedParameters_theta hθ hna hnv
  have ham := lowerUnmaskedParameters_amplitude hθ hna hnv
  refine ⟨ht,ham,?_⟩
  unfold SymmetricFamilyParameters.variance
  rw [lowerUnmaskedSequence_pi,show (lowerUnmaskedSequence a m n).theta = _ from ht,
    show (lowerUnmaskedSequence a m n).amplitude = _ from ham,mul_one]

theorem tendsto_lowerUnmaskedSequence_variance {a : ℕ → ℝ} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0)) :
    Tendsto (fun n => (lowerUnmaskedSequence a m n).variance) atTop (𝓝 0) := by
  apply (tendsto_lowerUnmasked_raw_variance hr hm hmTop hsmall).congr'
  filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hsmall] with n hn
  exact hn.2.2.symm

theorem tendsto_lowerUnmaskedSequence_widthScale {a : ℕ → ℝ} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0)) :
    Tendsto (fun n => lowerFamilyWidthScale (lowerUnmaskedSequence a m n) n (r n) (m n)) atTop (𝓝 0) := by
  apply hsmall.congr'
  filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hsmall] with n hn
  simp only [lowerFamilyWidthScale,lowerWidthScale,hn.2.1]

theorem tendsto_lowerUnmaskedSequence_rare_width {a : ℕ → ℝ} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (lowerUnmaskedSequence a m n).variance*
      independentAbsGaussianMean (m n)) atTop (𝓝 0) := by
  obtain ⟨c,hc,hg⟩ := exists_absoluteGaussianMean_sqrt_lower
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hbound : Tendsto (fun n : ℕ => (2/c)*lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (2/c)
  apply squeeze_zero' _ _ hbound
  · exact Eventually.of_forall (fun n => mul_nonneg (Real.sqrt_nonneg _)
      (independentAbsGaussianMean_nonneg _))
  · filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hsmall,ha,
      hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with n hnFields hna hnL hn
    rw [hnFields.2.2]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hm1 : 1 ≤ m n := by have := hm n; omega
    have hG := independentAbsGaussianMean_upper hm1
    rw [dimensionLog_eq_one_add_log hm1] at hG
    apply (mul_le_mul_of_nonneg_left hG (Real.sqrt_nonneg _)).trans
    exact lowerWidthBudget_gaussian_profile hna hnL hn0 (log_exp_mul_nat_ge_one (hr n)) hc
      (hg (r n) (hr n)) (by positivity) (lowerUnmasked_count_identity hn)

end
end RectangleCLTArxivV1

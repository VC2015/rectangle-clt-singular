import RectangleCLTCompanion.FourthIdentityRows

/-! Absolute scalar-kernel estimates for the exact fourth-order identity.
These are independent of analytic restoration and do not assert a CLT. -/

open scoped Interval

namespace RectangleCLT.Companion

noncomputable section

theorem abs_fourthKernel_le_one {t r : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |fourthKernel t r| ≤ 1 := by
  have hlin0 : 0 ≤ (3 - t) * r := mul_nonneg (by linarith) hr
  have hlin1 : (3 - t) * r ≤ 3 - t := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 3 - t) (sub_nonneg.mpr hr1)]
  have habs : |(3 - t) * r - 2 * t| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hpow0 : 0 ≤ (1 - r) ^ 2 := sq_nonneg _
  have hpow1 : (1 - r) ^ 2 ≤ 1 := by nlinarith
  have hfac0 : 0 ≤ (1 + t) / 6 * (1 - r) ^ 2 := by positivity
  have hfac1 : (1 + t) / 6 * (1 - r) ^ 2 ≤ 1 / 3 := by
    calc
      _ ≤ (1 + t) / 6 * 1 := mul_le_mul_of_nonneg_left hpow1 (by positivity)
      _ ≤ _ := by linarith
  unfold fourthKernel
  rw [abs_mul, abs_of_nonneg hfac0]
  calc
    _ ≤ (1 / 3 : ℝ) * 3 := mul_le_mul hfac1 habs (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem abs_fourthKernel_integral_le (f : ℝ → ℝ) {t K : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (_hK : 0 ≤ K)
    (hf : ∀ r ∈ Set.Icc (0 : ℝ) 1, |f r| ≤ K) :
    |∫ r in (0 : ℝ)..1, fourthKernel t r * f r| ≤ K := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := K)
    (f := fun r => fourthKernel t r * f r) (fun r hr => ?_)
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh
  · rw [Set.uIoc_of_le (by norm_num)] at hr
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_fourthKernel_le_one ht ht1 hr.1.le hr.2)
      (hf r ⟨hr.1.le, hr.2⟩) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem abs_linearKernel_integral_le (f : ℝ → ℝ) {K : ℝ}
    (_hK : 0 ≤ K) (hf : ∀ r ∈ Set.Icc (0 : ℝ) 1, |f r| ≤ K) :
    |∫ r in (0 : ℝ)..1, (1 - r) * f r| ≤ K := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := K)
    (f := fun r => (1 - r) * f r) (fun r hr => ?_)
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh
  · rw [Set.uIoc_of_le (by norm_num)] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr.2)]
    exact (mul_le_mul (by linarith [hr.1] : 1 - r ≤ 1)
      (hf r ⟨hr.1.le, hr.2⟩) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem abs_unitInterval_integral_le (f : ℝ → ℝ) {K : ℝ}
    (hf : ∀ r ∈ Set.Icc (0 : ℝ) 1, |f r| ≤ K) :
    |∫ r in (0 : ℝ)..1, f r| ≤ K := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := K)
    (f := f) (fun r hr => ?_)
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh
  · rw [Set.uIoc_of_le (by norm_num)] at hr
    exact hf r ⟨hr.1.le, hr.2⟩

theorem thirdCorrection_coefficient_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ t * (1 - t) / (3 * (1 + t)) ∧
      t * (1 - t) / (3 * (1 + t)) ≤ t / 3 := by
  have hn : 0 < 3 * (1 + t) := by positivity
  constructor
  · exact div_nonneg (mul_nonneg ht (sub_nonneg.mpr ht1)) hn.le
  · apply (div_le_iff₀ hn).mpr
    nlinarith [sq_nonneg t]

theorem abs_thirdCorrection_integral_le (f : ℝ → ℝ) {t K : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (_hK : 0 ≤ K)
    (hf : ∀ r ∈ Set.Icc (0 : ℝ) 1, |f r| ≤ K) :
    |t * (1 - t) / (3 * (1 + t)) * (∫ r in (0 : ℝ)..1, f r)| ≤ t / 3 * K := by
  rw [abs_mul, abs_of_nonneg (thirdCorrection_coefficient_le ht ht1).1]
  exact mul_le_mul (thirdCorrection_coefficient_le ht ht1).2
    (abs_unitInterval_integral_le f hf) (abs_nonneg _) (by positivity)

/-- Uniform control of the actual derivative integrands gives the desired
fourth-order remainder estimate, with no loss from the scalar kernels. -/
theorem abs_fourthIntegralCombination_le (fA fB fC : ℝ → ℝ) {t K : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (hA : ∀ r ∈ Set.Icc (0 : ℝ) 1, |fA r| ≤ K)
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) 1, |fB r| ≤ K)
    (hC : ∀ r ∈ Set.Icc (0 : ℝ) 1, |fC r| ≤ K) :
    |(∫ r in (0 : ℝ)..1, fourthKernel t r * fA r) +
      (1 - t) / 2 * (∫ r in (0 : ℝ)..1, (1 - r) * fB r) +
      t * (1 - t) / (3 * (1 + t)) * (∫ r in (0 : ℝ)..1, fC r)| ≤ 2 * K := by
  have hA' := abs_fourthKernel_integral_le fA ht ht1 hK hA
  have hC' := abs_thirdCorrection_integral_le fC ht ht1 hK hC
  have hB' : |(1 - t) / 2 * (∫ r in (0 : ℝ)..1, (1 - r) * fB r)| ≤ K / 2 := by
    rw [abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr ht1) (by norm_num))]
    have hh := mul_le_mul (by linarith : (1 - t) / 2 ≤ 1 / 2)
      (abs_linearKernel_integral_le fB hK hB) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith
  exact ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)).trans (by
    nlinarith [mul_le_mul_of_nonneg_right ht1 hK])

end
end RectangleCLT.Companion

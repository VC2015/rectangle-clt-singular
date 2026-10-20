import RectangleCLT.GaussianDerivativeScaling
import RectangleCLT.GaussianFourthFaceBounds

/-! Exact covariance scaling and scalar variance-time estimates for the
fourth Gaussian derivative bounds. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem matrixQuadratic_smul {p : ℕ} (a : ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    matrixQuadratic (a • Q) x = a * matrixQuadratic Q x := by
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem LocalCovarianceLower.smul {p r : ℕ} {Q : Matrix (Fin p) (Fin p) ℝ}
    {a b : ℝ} (h : LocalCovarianceLower Q r a) (hb : 0 ≤ b) :
    LocalCovarianceLower (b • Q) r (b * a) := by
  intro x hx
  rw [matrixQuadratic_smul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (h x hx) hb

theorem sqrt_smul_mul_transpose {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 ≤ v) :
    (Real.sqrt v • A) * (Real.sqrt v • A).transpose = v • (A * A.transpose) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  nlinarith [Real.sq_sqrt hv]

theorem sqrt_smul_mul_transpose_diagonal {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {v : ℝ} (hv : 0 ≤ v) (j : Fin p) :
    ((Real.sqrt v • A) * (Real.sqrt v • A).transpose) j j = v := by
  rw [sqrt_smul_mul_transpose A hv, Matrix.smul_apply, smul_eq_mul, hdiag, mul_one]

theorem scaled_normalMatrix_gram_det_isUnit {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₄ v : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha₄ : 0 < a₄)
    (hv : 0 < v) (hq : q ≤ 4) :
    IsUnit ((GaussianTube.normalMatrix S (Real.sqrt v • A)).transpose *
      GaussianTube.normalMatrix S (Real.sqrt v • A)).det := by
  apply GaussianTube.normalMatrix_gram_det_isUnit S _
    (a := v * a₄) _ (mul_pos hv ha₄)
  rw [sqrt_smul_mul_transpose A hv.le]
  exact (hQ.mono hq).smul hv.le

theorem inverse_sqrt_one_sub_le_sqrt_two {t : ℝ} (ht : t ≤ 1 / 2) :
    1 / Real.sqrt (1 - t) ≤ Real.sqrt 2 := by
  have hroot := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ≤ 1 - t by linarith)
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one] at hroot
  have ht0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  simpa only [one_div_one_div] using
    one_div_le_one_div_of_le (div_pos zero_lt_one ht0) hroot

theorem bounded_step_mul_sqrt_log_le {δ h L t : ℝ} (hδ : 0 ≤ δ)
    (hδh : δ ≤ h) (hL : 0 ≤ L) (hband : h ^ 2 * L ≤ t) :
    δ * Real.sqrt L ≤ Real.sqrt t := by
  have hδsq : δ ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hδ hδh 2
  have ht : 0 ≤ t := (mul_nonneg (sq_nonneg h) hL).trans hband
  apply (sq_le_sq₀ (mul_nonneg hδ (Real.sqrt_nonneg L)) (Real.sqrt_nonneg t)).mp
  rw [mul_pow, Real.sq_sqrt hL, Real.sq_sqrt ht]
  exact (mul_le_mul_of_nonneg_right hδsq hL).trans hband

/-- The concrete localized tube factor in the short Gaussian-time regime.
The doubled envelope is the one produced by the actual Bernoulli-thinned
bounded arrays. -/
theorem fourth_localization_factor_le {δ h L t : ℝ} (hδ : 0 ≤ δ)
    (hδh : δ ≤ h) (hL : 0 ≤ L) (hband : h ^ 2 * L ≤ t) (ht : t ≤ 1 / 2) :
    (Real.sqrt t + 2 * δ * Real.sqrt L) / Real.sqrt (1 - t) ≤
      3 * Real.sqrt 2 * Real.sqrt t := by
  have hstep := bounded_step_mul_sqrt_log_le hδ hδh hL hband
  have hnum : Real.sqrt t + 2 * δ * Real.sqrt L ≤ 3 * Real.sqrt t := by linarith
  calc
    _ ≤ (3 * Real.sqrt t) / Real.sqrt (1 - t) :=
      div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
    _ ≤ (3 * Real.sqrt t) * Real.sqrt 2 := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using mul_le_mul_of_nonneg_left
        (inverse_sqrt_one_sub_le_sqrt_two ht)
        (mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (Real.sqrt_nonneg t))
    _ = _ := by ring

theorem normalized_localization_factor_eq {t η L : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (1 + (η / Real.sqrt t) * Real.sqrt L) / Real.sqrt ((1 - t) / t) =
      (Real.sqrt t + η * Real.sqrt L) / Real.sqrt (1 - t) := by
  rw [Real.sqrt_div (sub_nonneg.mpr ht1.le)]
  have ht0 : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have hr0 : Real.sqrt (1 - t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr ht1))
  field_simp [ht0, hr0]

theorem sqrt_div_square_eq_inv_rpow {t : ℝ} (ht : 0 < t) :
    Real.sqrt t / t ^ 2 = 1 / t ^ (3 / 2 : ℝ) := by
  have hc : (Real.sqrt t) ^ 3 = t ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le (1 / 2 : ℝ) 3]
    norm_num
  have hroot : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  rw [← hc]
  apply (div_eq_div_iff (pow_ne_zero 2 ht.ne') (pow_ne_zero 3 hroot)).mpr
  calc
    _ = ((Real.sqrt t) ^ 2) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt ht.le]; ring

/-- The short-time localization gain cancels one square-root power from the
fourth derivative's exact variance scaling. -/
theorem fourth_localization_div_square_le {δ h L t : ℝ} (hδ : 0 ≤ δ)
    (hδh : δ ≤ h) (hL : 0 ≤ L) (hband : h ^ 2 * L ≤ t)
    (ht : 0 < t) (hthalf : t ≤ 1 / 2) :
    ((Real.sqrt t + 2 * δ * Real.sqrt L) / Real.sqrt (1 - t)) / t ^ 2 ≤
      3 * Real.sqrt 2 / t ^ (3 / 2 : ℝ) := by
  calc
    _ ≤ (3 * Real.sqrt 2 * Real.sqrt t) / t ^ 2 :=
      div_le_div_of_nonneg_right (fourth_localization_factor_le hδ hδh hL hband hthalf) (sq_nonneg t)
    _ = (3 * Real.sqrt 2) * (Real.sqrt t / t ^ 2) := by ring
    _ = _ := by rw [sqrt_div_square_eq_inv_rpow ht]; ring

theorem normalized_fourth_localization_div_square_le {δ h L t : ℝ} (hδ : 0 ≤ δ)
    (hδh : δ ≤ h) (hL : 0 ≤ L) (hband : h ^ 2 * L ≤ t)
    (ht : 0 < t) (hthalf : t ≤ 1 / 2) :
    ((1 + ((2 * δ) / Real.sqrt t) * Real.sqrt L) /
      Real.sqrt ((1 - t) / t)) / t ^ 2 ≤
      3 * Real.sqrt 2 / t ^ (3 / 2 : ℝ) := by
  rw [normalized_localization_factor_eq ht (by linarith : t < 1)]
  exact fourth_localization_div_square_le hδ hδh hL hband ht hthalf

theorem inverse_square_le_four {t : ℝ} (ht : 1 / 2 ≤ t) : 1 / t ^ 2 ≤ 4 := by
  have ht0 : 0 < t := by linarith
  have hs : (1 / 2 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht 2
  apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
  nlinarith

theorem one_div_rpow_three_halves_eq_neg {t : ℝ} (ht : 0 ≤ t) :
    1 / t ^ (3 / 2 : ℝ) = t ^ (-(3 / 2 : ℝ)) := by
  rw [Real.rpow_neg ht, one_div]

theorem inverse_square_le_four_mul_neg_three_halves {t : ℝ}
    (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    1 / t ^ 2 ≤ 4 * t ^ (-(3 / 2 : ℝ)) := by
  apply (inverse_square_le_four ht).trans
  have hr := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (show 0 < t by linarith) ht1 (show -(3 / 2 : ℝ) ≤ 0 by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 4 by norm_num)

end
end RectangleCLT

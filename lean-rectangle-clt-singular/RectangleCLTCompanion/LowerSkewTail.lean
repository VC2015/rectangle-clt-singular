import RectangleCLTCompanion.LowerCramerNormalized
import RectangleCLTCompanion.LowerSkewScales

/-! The actual skewed scalar tail at the exact Gaussian maximum
threshold. The error is negligible relative to the manuscript rate,
without a limit assumption on the standardized skewness coefficient. -/

open Filter

namespace RectangleCLT.Companion

noncomputable section

def lowerSkewLogTail (B : ℝ) (p n : ℕ) : ℝ :=
  Real.log (lowerCoordinateUpperTail B n (normalMaxThreshold p) /
    standardNormalUpperTail (normalMaxThreshold p))

def lowerSkewCoefficient (B : ℝ) : ℝ :=
  (1 - 1 / B ^ 2) * Real.sqrt 2 / 3

theorem lowerSkewRate_eventually_pos {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop) :
    ∀ᶠ n in atTop, 0 < lowerSkewRate (B n) (p n) n := by
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hp' hn
  have hBp : 0 < B n := by linarith only [hB n]
  have hlog : 0 < Real.log (p n : ℝ) := Real.log_pos (by exact_mod_cast hp')
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (mul_pos hBp (Real.rpow_pos_of_pos hlog _)) (Real.sqrt_pos.mpr hnR)

theorem lowerSkew_cramer_eventually {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (nhds r₀)) :
    ∀ᶠ n in atTop, 0 < lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) ∧
      |lowerSkewLogTail (B n) (p n) n -
        (B n - (B n)⁻¹) * normalMaxThreshold (p n) ^ 3 / (6 * Real.sqrt n)| ≤
        lowerCramerRemainderConstant * (B n * normalMaxThreshold (p n) / Real.sqrt n +
          (B n) ^ 2 * normalMaxThreshold (p n) ^ 4 / n) := by
  have hx := (tendsto_normalMaxThreshold_atTop.comp hp).eventually (eventually_ge_atTop 2)
  have hs := (lower_skew_linear_scale hp hr).const_mul lowerCramerSmallConstant
  simp only [mul_zero] at hs
  have hsmall : ∀ᶠ n in atTop, lowerCramerSmallConstant *
      (B n * (normalMaxThreshold (p n) / Real.sqrt n)) ≤ 1 := by
    have hh := hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hh] with n hn
    simpa only [mul_div_assoc] using hn.le
  filter_upwards [hx, hsmall, eventually_ge_atTop 1] with n hxn hsn hn
  have hBn : 1 ≤ B n := by linarith only [hB n]
  refine ⟨lowerCoordinateUpperTail_cramer_pos hBn hn hxn hsn, ?_⟩
  simpa only [lowerSkewLogTail, mul_div_assoc] using
    lowerCoordinateUpperTail_cramer_bound hBn hn hxn hsn

theorem lowerSkew_log_tail_remainder_ratio {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (nhds r₀)) :
    Tendsto (fun n => (lowerSkewLogTail (B n) (p n) n -
      (B n - (B n)⁻¹) * normalMaxThreshold (p n) ^ 3 / (6 * Real.sqrt n)) /
        lowerSkewRate (B n) (p n) n) atTop (nhds 0) := by
  have hz := ((lower_skew_linear_remainder_ratio hB hp).add
    (lower_skew_quartic_remainder_ratio hB hp hr)).const_mul lowerCramerRemainderConstant
  simp only [zero_add, mul_zero] at hz
  apply squeeze_zero_norm' _ hz
  filter_upwards [lowerSkew_cramer_eventually hB hp hr,
    lowerSkewRate_eventually_pos hB hp] with n hn hnr
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hnr]
  exact (div_le_div_of_nonneg_right hn.2 hnr.le).trans_eq (by ring)

theorem lowerSkew_log_tail_normalized {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (nhds r₀)) :
    Tendsto (fun n => lowerSkewLogTail (B n) (p n) n / lowerSkewRate (B n) (p n) n -
      lowerSkewCoefficient (B n)) atTop (nhds 0) := by
  have hh := (lowerSkew_log_tail_remainder_ratio hB hp hr).add
    (lower_skew_cubic_coefficient_difference hB hp)
  simp only [zero_add] at hh
  apply hh.congr
  intro n
  unfold lowerSkewCoefficient
  ring

theorem lowerSkewCoefficient_bounds {B : ℝ} (hB : 2 ≤ B) :
    Real.sqrt 2 / 4 ≤ lowerSkewCoefficient B ∧ lowerSkewCoefficient B ≤ Real.sqrt 2 / 3 := by
  have hBp : 0 < B := by linarith
  have hsq : 4 ≤ B^2 := by nlinarith
  have hinv : 1 / B^2 ≤ 1/4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hBp)).mpr
    linarith
  have hnonneg : 0 ≤ 1 / B^2 := by positivity
  have hsqrt := Real.sqrt_nonneg (2 : ℝ)
  unfold lowerSkewCoefficient
  constructor <;> nlinarith

end

end RectangleCLT.Companion

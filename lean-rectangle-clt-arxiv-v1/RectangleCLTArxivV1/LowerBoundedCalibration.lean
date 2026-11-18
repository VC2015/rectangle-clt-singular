import RectangleCLTArxivV1.LowerUnmaskedProfile

/-! Scalar calibration of the growing bounded envelope. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lower_dimensionLog_product {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    dimensionLog (r*m) = 1+Real.log (r : ℝ)+Real.log (m : ℝ) := by
  rw [dimensionLog_eq_one_add_log (by nlinarith : 1 ≤ r*m),Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (by omega : r ≠ 0)) (by exact_mod_cast (by omega : m ≠ 0))]
  ring

theorem lower_rareLog_le_dimensionLog {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    Real.log (m : ℝ) ≤ dimensionLog (r*m) := by
  rw [lower_dimensionLog_product hr hm]
  have hh : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hr)
  linarith

theorem lower_dimensionLog_le_three_rareLog {r m : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m)
    (hL : 1 ≤ Real.log (m : ℝ)) : dimensionLog (r*m) ≤ 3*Real.log (m : ℝ) := by
  rw [lower_dimensionLog_product hr (by omega)]
  have hh := Real.log_le_log (by exact_mod_cast hr : (0 : ℝ) < r) (by exact_mod_cast hrm : (r : ℝ) ≤ m)
  linarith

theorem tendsto_lower_bounded_raw_width_scale {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hsmall : Tendsto (fun n : ℕ => B n*independentAbsGaussianMean (r n)*dimensionLog (r n*m n)/Real.sqrt n)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => lowerWidthScale (B n-1) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hsmall
  · exact Eventually.of_forall (fun n => by
      unfold lowerWidthScale
      exact div_nonneg (mul_nonneg (mul_nonneg (by linarith [hB n])
        (Real.log_nonneg (by exact_mod_cast (by have := hm n; omega : 1 ≤ m n))))
        (independentAbsGaussianMean_nonneg _)) (Real.sqrt_nonneg _))
  · exact Eventually.of_forall (fun n => by
      unfold lowerWidthScale
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hL := lower_rareLog_le_dimensionLog (m := m n) (hr n) (by have := hm n; omega)
      have h1 := mul_le_mul_of_nonneg_left hL
        (mul_nonneg (show 0 ≤ B n-1 by linarith [hB n]) (independentAbsGaussianMean_nonneg (r n)))
      have h2 := mul_le_mul_of_nonneg_right (show B n-1 ≤ B n by linarith)
        (mul_nonneg (independentAbsGaussianMean_nonneg (r n))
          (zero_le_one.trans (log_exp_mul_nat_ge_one (by nlinarith [hr n,hm n] : 1 ≤ r n*m n))))
      change (B n-1)*(independentAbsGaussianMean (r n)*dimensionLog (r n*m n)) ≤
        B n*(independentAbsGaussianMean (r n)*dimensionLog (r n*m n)) at h2
      calc
        _ = ((B n-1)*independentAbsGaussianMean (r n))*Real.log (m n : ℝ) := by ring
        _ ≤ ((B n-1)*independentAbsGaussianMean (r n))*dimensionLog (r n*m n) := h1
        _ ≤ _ := by convert h2 using 1 <;> ring)

theorem lower_bounded_target_le_twelve_scale {B G g ell L N : ℝ}
    (hB : 2 ≤ B) (hG0 : 0 ≤ G) (hg : 0 ≤ g) (hG : G ≤ 2*g)
    (hell : 0 ≤ ell) (hL0 : 0 ≤ L) (hL : L ≤ 3*ell) :
    B*G*L/Real.sqrt N ≤ 12*lowerWidthScale (B-1) ell g N := by
  have hBa : B ≤ 2*(B-1) := by linarith
  have hBG := mul_le_mul hBa hG hG0 (by linarith : 0 ≤ 2*(B-1))
  have hBGL := mul_le_mul hBG hL hL0 (mul_nonneg (by linarith : 0 ≤ 2*(B-1)) (mul_nonneg (by norm_num) hg))
  have hh := div_le_div_of_nonneg_right hBGL (Real.sqrt_nonneg N)
  unfold lowerWidthScale
  convert hh using 1 <;> ring

end
end RectangleCLTArxivV1

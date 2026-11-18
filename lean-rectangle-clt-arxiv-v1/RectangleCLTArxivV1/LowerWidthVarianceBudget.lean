import RectangleCLTArxivV1.LowerWidthBudget

/-! Actual count identities imply the variance and Gaussian-width
calibrations used by the unmasked lower construction. -/

namespace RectangleCLTArxivV1
noncomputable section
set_option autoImplicit false

private theorem lowerWidthBudget_count_identity {theta ell n : ℝ}
    (hn : 0 < n) (hcount : n * theta = ell / 2) : theta = ell / (2 * n) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hn.ne')).mpr
  nlinarith only [hcount]

private theorem lowerWidthBudget_leading_square {a ell g n R c : ℝ}
    (hn : 0 < n) (hR : 1 ≤ R) (hc : 0 < c) (hg : c * Real.sqrt R ≤ g) :
    a ^ 2 * ell ^ 2 / n ≤ lowerWidthScale a ell g n ^ 2 / c ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right hR
    (div_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg ell)) hn.le)
  calc
    _ ≤ R * a ^ 2 * ell ^ 2 / n := by convert hmul using 1 <;> ring
    _ ≤ _ := lowerWidthBudget_shift_square hn (zero_le_one.trans hR) hc hg

theorem lowerWidthBudget_variance {a ell g n R c theta : ℝ}
    (hell : 1 ≤ ell) (hn : 0 < n) (hR : 1 ≤ R)
    (hc : 0 < c) (hg : c * Real.sqrt R ≤ g)
    (hcount : n * theta = ell / 2) :
    theta * a ^ 2 ≤ lowerWidthScale a ell g n ^ 2 / (2 * c ^ 2) := by
  have hell2 : ell ≤ ell ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hell2 (div_nonneg (sq_nonneg a) hn.le)
  have hsmall : 2 * (theta * a ^ 2) ≤ a ^ 2 * ell ^ 2 / n := by
    rw [lowerWidthBudget_count_identity hn hcount]
    convert hm using 1 <;> ring
  have hfull := hsmall.trans (lowerWidthBudget_leading_square hn hR hc hg)
  calc
    theta * a ^ 2 ≤ (lowerWidthScale a ell g n ^ 2 / c ^ 2) / 2 := by linarith only [hfull]
    _ = _ := by ring

theorem lowerWidthBudget_gaussian_profile {a ell g n R c theta : ℝ}
    (ha : 1 ≤ a) (hell : 1 ≤ ell) (hn : 0 < n) (hR : 1 ≤ R)
    (hc : 0 < c) (hg : c * Real.sqrt R ≤ g) (htheta : 0 ≤ theta)
    (hcount : n * theta = ell / 2) :
    Real.sqrt (theta * a ^ 2) * (2 * Real.sqrt (1 + ell)) ≤
      (2 / c) * lowerWidthScale a ell g n := by
  have hg0 : 0 ≤ g := (mul_nonneg hc.le (Real.sqrt_nonneg R)).trans hg
  have hscale : 0 ≤ lowerWidthScale a ell g n := by
    unfold lowerWidthScale
    positivity
  have hrhs : 0 ≤ (2 / c) * lowerWidthScale a ell g n := by positivity
  have hnonneg : 0 ≤ theta * a ^ 2 := mul_nonneg htheta (sq_nonneg a)
  have hell0 : 0 ≤ 1 + ell := by linarith
  have hL : ell * (1 + ell) ≤ 2 * ell ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hL
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg a)) hn.le)
  have hleft : 4 * (theta * a ^ 2) * (1 + ell) ≤ 4 * (a ^ 2 * ell ^ 2 / n) := by
    rw [lowerWidthBudget_count_identity hn hcount]
    convert hm using 1 <;> ring
  have hcore := mul_le_mul_of_nonneg_left
    (lowerWidthBudget_leading_square (a := a) (ell := ell) hn hR hc hg)
    (by norm_num : (0 : ℝ) ≤ 4)
  have hsquare : (Real.sqrt (theta * a ^ 2) * (2 * Real.sqrt (1 + ell))) ^ 2 ≤
      ((2 / c) * lowerWidthScale a ell g n) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnonneg, Real.sq_sqrt hell0]
    convert hleft.trans hcore using 1 <;> ring
  nlinarith only [hsquare, hrhs]

end
end RectangleCLTArxivV1

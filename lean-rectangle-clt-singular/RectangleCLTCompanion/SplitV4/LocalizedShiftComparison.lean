import RectangleCLTCompanion.SplitV4.ShiftComparison

/-! Signed-shift comparison requiring the approximating CDF only near the tested threshold. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem shifted_taylor_bound_local (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) {B r t y : ℝ}
    (hB : ∀ x, |x-t| ≤ r → |deriv (deriv F) x| ≤ B) (hy : |y| ≤ r) :
    |F (t-y) - F t + deriv F t * y| ≤ (B / 2) * y ^ 2 := by
  have hF1 : ContDiff ℝ 1 (deriv F) := (contDiff_succ_iff_deriv.mp hF).2.2
  have hD := hF.differentiable (by norm_num)
  have hD1 := hF1.differentiable (by norm_num)
  let f : ℝ → ℝ := fun u => F (t-u*y)
  have hfc : ContDiff ℝ 2 f := hF.comp (contDiff_const.sub (contDiff_id.mul contDiff_const))
  have hd (u : ℝ) : HasDerivAt f (-y * deriv F (t-u*y)) u := by
    convert (hD (t-u*y)).hasDerivAt.comp u (((hasDerivAt_id u).mul_const y).const_sub t) using 1
    dsimp only [f]
    ring
  have hd1 (u : ℝ) : HasDerivAt (fun z => -y * deriv F (t-z*y))
      (y^2 * deriv (deriv F) (t-u*y)) u := by
    convert ((hD1 (t-u*y)).hasDerivAt.comp u (((hasDerivAt_id u).mul_const y).const_sub t)).const_mul (-y) using 1
    ring
  have he1 : deriv f = fun u => -y * deriv F (t-u*y) := funext (fun u => (hd u).deriv)
  have he2 (u : ℝ) : iteratedDeriv 2 f u = y^2 * deriv (deriv F) (t-u*y) := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [he1]
    exact (hd1 u).deriv
  obtain ⟨u, hu, hrem⟩ := taylor1_mean_remainder hfc
  have hlocal : |(t-u*y)-t| ≤ r := by
    rw [show (t-u*y)-t = -(u*y) by ring, abs_neg, abs_mul, abs_of_nonneg hu.1.le]
    exact (mul_le_mul_of_nonneg_right hu.2.le (abs_nonneg y)).trans (by simpa only [one_mul] using hy)
  have heq : F (t-y) - F t + deriv F t * y = (y^2 * deriv (deriv F) (t-u*y)) / 2 := by
    rw [he2, iteratedDeriv_one, he1] at hrem
    norm_num only [f, one_mul, zero_mul, sub_zero] at hrem
    linarith
  rw [heq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg y), abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hB _ hlocal) (sq_nonneg y)) (by norm_num)).trans_eq (by ring)

def localShiftTaylorCost (B r d : ℝ) : ℝ := B / 2 + 1 / r ^ 2 + |d| / r

theorem shifted_taylor_bound_local_global (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) {B r t : ℝ}
    (hB0 : 0 ≤ B) (hr : 0 < r) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hB : ∀ x, |x-t| ≤ r → |deriv (deriv F) x| ≤ B) (y : ℝ) :
    |F (t-y) - F t + deriv F t * y| ≤ localShiftTaylorCost B r (deriv F t) * y ^ 2 := by
  have hpad : 0 ≤ (1 / r ^ 2 + |deriv F t| / r) * y ^ 2 := by positivity
  by_cases hy : |y| ≤ r
  · have hh := shifted_taylor_bound_local F hF hB hy
    unfold localShiftTaylorCost
    nlinarith only [hh, hpad]
  · have hry : r ≤ |y| := le_of_lt (lt_of_not_ge hy)
    have hsq : r ^ 2 ≤ y ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ hr.le hry 2
    have h1 : 1 ≤ y ^ 2 / r ^ 2 := (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa using hsq)
    have h2 : |y| ≤ y ^ 2 / r := by
      apply (le_div_iff₀ hr).mpr
      have hh := mul_le_mul_of_nonneg_right hry (abs_nonneg y)
      nlinarith only [hh, sq_abs y]
    have hFdiff : |F (t-y) - F t| ≤ 1 := abs_le.mpr ⟨by linarith [hF0 (t-y), hF1 t], by linarith [hF0 t, hF1 (t-y)]⟩
    have hh := (abs_add (F (t-y)-F t) (deriv F t*y)).trans (add_le_add_right hFdiff _)
    rw [abs_mul] at hh
    have hd := mul_le_mul_of_nonneg_left h2 (abs_nonneg (deriv F t))
    have hb : 0 ≤ (B / 2) * y ^ 2 := by positivity
    calc
      _ ≤ 1 + |deriv F t| * |y| := hh
      _ ≤ y ^ 2 / r ^ 2 + |deriv F t| * (y ^ 2 / r) := add_le_add h1 hd
      _ = (1 / r ^ 2 + |deriv F t| / r) * y ^ 2 := by ring
      _ ≤ _ := by unfold localShiftTaylorCost; nlinarith only [hb]

end
end RectangleCLT.Companion.SplitV4

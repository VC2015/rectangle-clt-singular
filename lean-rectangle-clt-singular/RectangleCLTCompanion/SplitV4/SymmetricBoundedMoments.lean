import RectangleCLTCompanion.SplitV4.SymmetricBoundedShiftLimits
import RectangleCLTCompanion.SubexponentialScales

/-! Genuine second-moment remainder budgets for the bounded symmetric lower family. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem bounded_shift_second_moment_budget {s N ell θ U2 V2 C : ℝ}
    (hs : 1 / 2 ≤ s) (hN : 0 < N) (hL : 1 ≤ ell) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hcount : N * θ = ell / 2)
    (hU : U2 ≤ (1 / (s * Real.sqrt N)) ^ 2 * ((N * θ) ^ 2 + N * θ))
    (hV : V2 ≤ (Real.sqrt θ / s) ^ 2 * (C * (1 + ell))) :
    U2 + V2 ≤ (3 + 4 * C) * ell ^ 2 / N := by
  have hspos : 0 < s := by linarith
  have hsqpos : 0 < s ^ 2 := sq_pos_of_pos hspos
  have hsq : 1 / 4 ≤ s ^ 2 := by nlinarith only [hs, sq_nonneg (s - 1 / 2)]
  have hL0 : 0 ≤ ell := by linarith
  have hnum : (ell / 2) ^ 2 + ell / 2 ≤ (3 / 4) * ell ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hL) hL0]
  have hU' : U2 ≤ 3 * ell ^ 2 / N := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hN.le, hcount] at hU
    have hq : ((ell / 2) ^ 2 + ell / 2) / s ^ 2 ≤ 3 * ell ^ 2 := by
      apply (div_le_iff₀ hsqpos).mpr
      nlinarith only [hnum, mul_le_mul_of_nonneg_right hsq (show 0 ≤ 3 * ell ^ 2 by positivity)]
    have hh := div_le_div_of_nonneg_right hq hN.le
    exact hU.trans (by convert hh using 1 <;> ring)
  have hinv : 1 / s ^ 2 ≤ 4 := (div_le_iff₀ hsqpos).mpr (by nlinarith only [hsq])
  have hV' : V2 ≤ 4 * C * ell ^ 2 / N := by
    rw [div_pow, Real.sq_sqrt hθ] at hV
    have hcoef : θ / s ^ 2 * (C * (1 + ell)) ≤ θ * 4 * (C * (2 * ell)) := by
      have h1 := mul_le_mul_of_nonneg_left hinv hθ
      have h2 := mul_le_mul_of_nonneg_left (by linarith : 1 + ell ≤ 2 * ell) hC
      have hh := mul_le_mul h1 h2 (mul_nonneg hC (by linarith)) (by positivity : 0 ≤ θ * 4)
      convert hh using 1 <;> ring
    apply (le_div_iff₀ hN).mpr
    have hh := mul_le_mul_of_nonneg_right (hV.trans hcoef) hN.le
    have heq : (θ * 4 * (C * (2 * ell))) * N = 4 * C * ell ^ 2 := by
      calc
        _ = 8 * C * ell * (N * θ) := by ring
        _ = _ := by rw [hcount]; ring
    exact hh.trans_eq heq
  exact (add_le_add hU' hV').trans_eq (by ring)

theorem eventually_boundedFamily_shift_second_moment_budget {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      familyShiftSecondMoments (boundedFamilyParameters n (m n)) n (m n) ≤
        (3 + 4 * Real.exp (11 / 2)) * Real.log (m n : ℝ) ^ 2 / n := by
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [boundedFamilyParameters_eventually_count hm hmTop hsmall,
    (tendsto_boundedFamily_scale hm hmTop hsmall).eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hlog.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with n hncount hns hnL hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
  have hU := familyObservationShift_sq_integral_le (boundedFamilyParameters n (m n)) n (m n)
  rw [boundedFamilyParameters_amplitude] at hU
  have hV := familyGaussianShift_sq_integral_le (boundedFamilyParameters n (m n)) (m n)
  rw [boundedFamilyParameters_variance, dimensionLog_eq_one_add_log (by have := hm n; omega)] at hV
  exact bounded_shift_second_moment_budget hns hnp hnL (boundedFamilyParameters n (m n)).theta_pos.le
    (Real.exp_pos _).le hncount hU hV

end
end RectangleCLT.Companion.SplitV4

import RectangleCLTCompanion.SplitV4.GaussianExtremeCalibration
import RectangleCLT.Optimization

/-! The global, three-region density-derivative argument printed at
frozen-manuscript lines 4135–4145, in addition to the pre-existing local
curvature bound. The constants are deliberately nonoptimal. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem nonneg_mul_exp_neg_le {z : ℝ} (hz : 0 ≤ z) :
    z * Real.exp (-z) ≤ 1 := by
  have h := Real.add_one_le_exp z
  have hh : z ≤ Real.exp z := by linarith
  calc
    _ ≤ Real.exp z * Real.exp (-z) := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; norm_num

theorem nonneg_sq_mul_exp_neg_half_le {z : ℝ} (hz : 0 ≤ z) :
    z ^ 2 * Real.exp (-z / 2) ≤ 16 := by
  have h := nonneg_mul_exp_neg_le (by positivity : 0 ≤ z / 4)
  have h0 : 0 ≤ z / 4 * Real.exp (-(z / 4)) := by positivity
  have hh := mul_self_le_mul_self h0 h
  have he : (z / 4 * Real.exp (-(z / 4))) ^ 2 =
      z ^ 2 * Real.exp (-z / 2) / 16 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * -(z / 4) = -z / 2 by ring]
    ring
  rw [← sq, he] at hh
  nlinarith

theorem nonneg_mul_exp_neg_half_le {z : ℝ} (hz : 0 ≤ z) :
    z * Real.exp (-z / 2) ≤ 2 := by
  have h := nonneg_mul_exp_neg_le (by positivity : 0 ≤ z / 2)
  have he : z * Real.exp (-z / 2) = 2 * (z / 2 * Real.exp (-(z / 2))) := by ring
  rw [he]
  linarith

theorem standardNormalPDF_le_at_zero (x : ℝ) :
    standardNormalPDF x ≤ standardNormalPDF 0 := by
  rw [standardNormalPDF_eq, standardNormalPDF_eq]
  simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

theorem abs_mul_standardNormalPDF_le_at_zero (x : ℝ) :
    |x| * standardNormalPDF x ≤ standardNormalPDF 0 := by
  have hx : |x| ≤ Real.exp (x ^ 2 / 2) := by
    have hs : |x| ≤ 1 + x ^ 2 / 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    linarith [Real.add_one_le_exp (x ^ 2 / 2)]
  have he : |x| * Real.exp (-x ^ 2 / 2) ≤ 1 := by
    calc
      _ ≤ Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [standardNormalPDF_eq, standardNormalPDF_eq]
  simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹)]

def gaussianMillsUniformConstant : ℝ :=
  standardNormalPDF 0 / standardNormalUpperTail 1 + 2

theorem gaussianMillsUniformConstant_pos : 0 < gaussianMillsUniformConstant := by
  unfold gaussianMillsUniformConstant
  have := standardNormalPDF_pos 0
  have := standardNormalUpperTail_pos 1
  positivity

theorem standardNormalPDF_le_uniform_mills {x : ℝ} (hx : 0 ≤ x) :
    standardNormalPDF x ≤
      gaussianMillsUniformConstant * (1 + x) * standardNormalUpperTail x := by
  have hq := standardNormalUpperTail_pos x
  have hq1 := standardNormalUpperTail_pos 1
  have hp := standardNormalPDF_pos 0
  by_cases hx1 : 1 ≤ x
  · have hx0 : 0 < x := by linarith
    have hm := (normal_mills_density_ratio_bounds hx0).2
    have ht := (div_le_iff₀ (mul_pos hx0 hq)).mp hm
    have hinv : 1 / x ≤ 1 := (div_le_one hx0).mpr hx1
    have he : (1 + 1 / x ^ 2) * (x * standardNormalUpperTail x) =
        (x + 1 / x) * standardNormalUpperTail x := by field_simp; ring
    rw [he] at ht
    have hC : 1 ≤ gaussianMillsUniformConstant := by
      unfold gaussianMillsUniformConstant
      have : 0 ≤ standardNormalPDF 0 / standardNormalUpperTail 1 := by positivity
      linarith
    have hh : x + 1 / x ≤ gaussianMillsUniformConstant * (1 + x) := by nlinarith
    exact ht.trans (mul_le_mul_of_nonneg_right hh hq.le)
  · have hx1 : x ≤ 1 := le_of_not_ge hx1
    have htail : standardNormalUpperTail 1 ≤ standardNormalUpperTail x := by
      rw [standardNormalUpperTail_eq_one_sub, standardNormalUpperTail_eq_one_sub]
      linarith [strictMono_standardNormalCDF.monotone hx1]
    have hm : standardNormalPDF 0 ≤
        (standardNormalPDF 0 / standardNormalUpperTail 1) * standardNormalUpperTail x := by
      calc
        _ = (standardNormalPDF 0 / standardNormalUpperTail 1) * standardNormalUpperTail 1 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)
    have hC : standardNormalPDF 0 / standardNormalUpperTail 1 ≤
        gaussianMillsUniformConstant * (1 + x) := by
      unfold gaussianMillsUniformConstant
      have hh : 0 ≤ standardNormalPDF 0 / standardNormalUpperTail 1 := by positivity
      nlinarith
    exact (standardNormalPDF_le_at_zero x).trans (hm.trans
      (mul_le_mul_of_nonneg_right hC hq.le))

theorem normalCDF_power_pred_le_exp_half_tail {m k : ℕ}
    (hmk : m ≤ 2 * k) (x : ℝ) :
    standardNormalCDF x ^ k ≤ Real.exp (-((m : ℝ) * standardNormalUpperTail x) / 2) := by
  have hmk' : (m : ℝ) ≤ 2 * k := by exact_mod_cast hmk
  have hq := (standardNormalUpperTail_pos x).le
  exact (normalMaximumCDF_le_exp_tail_mass k x).trans
    (Real.exp_le_exp.mpr (by nlinarith))

/-- The printed `w+w²` exponential damping estimate. Keeping both tail
factors makes the estimate uniform in the number of independent normals. -/
theorem normalMaximumDensity_derivative_tail_envelope {m : ℕ} (hm : 4 ≤ m)
    (x P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hp : standardNormalPDF x ≤ P * standardNormalUpperTail x)
    (hxp : |x| * standardNormalPDF x ≤ Q * standardNormalUpperTail x) :
    |deriv (normalMaximumDensity m) x| ≤ 16 * P ^ 2 + 2 * Q := by
  let w := (m : ℝ) * standardNormalUpperTail x
  have htail0 := (standardNormalUpperTail_pos x).le
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (0 : ℝ) ≤ m - 1 := by
    have : (4 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hp0 := (standardNormalPDF_pos x).le
  have hc0 := standardNormalCDF_nonneg x
  have hpow2 := normalCDF_power_pred_le_exp_half_tail (m := m) (k := m - 2) (by omega) x
  have hpow1 := normalCDF_power_pred_le_exp_half_tail (m := m) (k := m - 1) (by omega) x
  change standardNormalCDF x ^ (m - 2) ≤ Real.exp (-w / 2) at hpow2
  change standardNormalCDF x ^ (m - 1) ≤ Real.exp (-w / 2) at hpow1
  have hmp : (m : ℝ) * standardNormalPDF x ≤ P * w := by
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_left hp hm0]
  have hfirst : (m : ℝ) * (m - 1) * standardNormalCDF x ^ (m - 2) *
      standardNormalPDF x ^ 2 ≤ 16 * P ^ 2 := by
    calc
      _ = ((m : ℝ) * (m - 1)) * standardNormalPDF x ^ 2 *
          standardNormalCDF x ^ (m - 2) := by ring
      _ ≤ (m : ℝ) ^ 2 * standardNormalPDF x ^ 2 * Real.exp (-w / 2) := by
        gcongr
        nlinarith
      _ = ((m : ℝ) * standardNormalPDF x) ^ 2 * Real.exp (-w / 2) := by ring
      _ ≤ (P * w) ^ 2 * Real.exp (-w / 2) := by gcongr
      _ = P ^ 2 * (w ^ 2 * Real.exp (-w / 2)) := by ring
      _ ≤ P ^ 2 * 16 := mul_le_mul_of_nonneg_left (nonneg_sq_mul_exp_neg_half_le hw) (sq_nonneg _)
      _ = _ := by ring
  have hsecond : |x * normalMaximumDensity m x| ≤ 2 * Q := by
    have hxmp : |x| * ((m : ℝ) * standardNormalPDF x) ≤ Q * w := by
      dsimp [w]
      nlinarith [mul_le_mul_of_nonneg_left hxp hm0]
    calc
      _ = (|x| * ((m : ℝ) * standardNormalPDF x)) * standardNormalCDF x ^ (m - 1) := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ normalMaximumDensity m x by
          unfold normalMaximumDensity; positivity)]
        unfold normalMaximumDensity
        ring
      _ ≤ (Q * w) * Real.exp (-w / 2) := by gcongr
      _ = Q * (w * Real.exp (-w / 2)) := by ring
      _ ≤ Q * 2 := mul_le_mul_of_nonneg_left (nonneg_mul_exp_neg_half_le hw) hQ
      _ = _ := by ring
  rw [(hasDerivAt_normalMaximumDensity (by omega : 2 ≤ m) x).deriv]
  have hfirst0 : 0 ≤ (m : ℝ) * (m - 1) * standardNormalCDF x ^ (m - 2) *
      standardNormalPDF x ^ 2 := by positivity
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg hfirst0]; linarith)

theorem normalMaximumDensity_derivative_negative_region {m : ℕ} (hm : 4 ≤ m)
    {x : ℝ} (hx : x ≤ 0) :
    |deriv (normalMaximumDensity m) x| ≤
      16 * (standardNormalPDF 0 / standardNormalUpperTail 0) ^ 2 +
        2 * (standardNormalPDF 0 / standardNormalUpperTail 0) := by
  have hq0 := standardNormalUpperTail_pos 0
  have hp0 := standardNormalPDF_pos 0
  have ht : standardNormalUpperTail 0 ≤ standardNormalUpperTail x := by
    rw [standardNormalUpperTail_eq_one_sub, standardNormalUpperTail_eq_one_sub]
    linarith [strictMono_standardNormalCDF.monotone hx]
  have hM : standardNormalPDF 0 ≤
      (standardNormalPDF 0 / standardNormalUpperTail 0) * standardNormalUpperTail x := by
    calc
      _ = (standardNormalPDF 0 / standardNormalUpperTail 0) * standardNormalUpperTail 0 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
  exact normalMaximumDensity_derivative_tail_envelope hm x _ _ (by positivity) (by positivity)
    ((standardNormalPDF_le_at_zero x).trans hM)
    ((abs_mul_standardNormalPDF_le_at_zero x).trans hM)

theorem normalMaximumDensity_derivative_positive_region {m : ℕ} (hm : 4 ≤ m)
    {x : ℝ} (hx : 0 ≤ x) :
    |deriv (normalMaximumDensity m) x| ≤
      (16 * gaussianMillsUniformConstant ^ 2 + 2 * gaussianMillsUniformConstant) * (1 + x) ^ 2 := by
  have hC := gaussianMillsUniformConstant_pos.le
  have h := normalMaximumDensity_derivative_tail_envelope hm x
    (gaussianMillsUniformConstant * (1 + x))
    (x * gaussianMillsUniformConstant * (1 + x)) (by positivity) (by positivity)
    (standardNormalPDF_le_uniform_mills hx) (by
      rw [abs_of_nonneg hx]
      nlinarith [mul_le_mul_of_nonneg_left (standardNormalPDF_le_uniform_mills hx) hx])
  apply h.trans
  have hh : x * (1 + x) ≤ (1 + x) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * gaussianMillsUniformConstant)]

theorem normalMaximumDensity_derivative_small_dimension {m : ℕ}
    (hm : 2 ≤ m) (hm3 : m ≤ 3) (x : ℝ) :
    |deriv (normalMaximumDensity m) x| ≤
      9 * standardNormalPDF 0 ^ 2 + 3 * standardNormalPDF 0 := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm3' : (m : ℝ) ≤ 3 := by exact_mod_cast hm3
  have hp0 := (standardNormalPDF_pos 0).le
  have hp := (standardNormalPDF_pos x).le
  have hmp : (m : ℝ) * standardNormalPDF x ≤ 3 * standardNormalPDF 0 := by
    exact (mul_le_mul_of_nonneg_left (standardNormalPDF_le_at_zero x) hm0).trans
      (mul_le_mul_of_nonneg_right hm3' hp0)
  have hxp : |x| * ((m : ℝ) * standardNormalPDF x) ≤ 3 * standardNormalPDF 0 := by
    nlinarith [mul_le_mul_of_nonneg_left (abs_mul_standardNormalPDF_le_at_zero x) hm0]
  exact (normalMaximumDensity_derivative_abs_le hm x).trans (by
    have hh := pow_le_pow_left₀ (mul_nonneg hm0 hp) hmp 2
    nlinarith)

theorem normalMaximumDensity_derivative_far_positive {m : ℕ} (hm : 2 ≤ m)
    {x : ℝ} (hx : 0 ≤ x) (hlog : Real.log (m : ℝ) ≤ x ^ 2 / 4) :
    |deriv (normalMaximumDensity m) x| ≤
      standardNormalPDF 0 ^ 2 + 2 * standardNormalPDF 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp0 := (standardNormalPDF_pos 0).le
  have hp := (standardNormalPDF_pos x).le
  have he : (m : ℝ) * standardNormalPDF x ≤
      standardNormalPDF 0 * Real.exp (-x ^ 2 / 4) := by
    have hPDF : standardNormalPDF x = standardNormalPDF 0 * Real.exp (-x ^ 2 / 2) := by
      rw [standardNormalPDF_eq, standardNormalPDF_eq]
      simp
    rw [hPDF]
    calc
      _ = standardNormalPDF 0 * Real.exp (Real.log (m : ℝ) - x ^ 2 / 2) := by
        rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring, Real.exp_neg,
          Real.exp_sub, Real.exp_log hm0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hp0
  have hmp : (m : ℝ) * standardNormalPDF x ≤ standardNormalPDF 0 := by
    exact he.trans (mul_le_of_le_one_right hp0
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])))
  have hxexp : x * Real.exp (-x ^ 2 / 4) ≤ 2 := by
    have hh : x / 2 ≤ Real.exp (x ^ 2 / 4) := by
      have := Real.add_one_le_exp (x ^ 2 / 4)
      nlinarith [sq_nonneg (x - 1)]
    have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x ^ 2 / 4)).le
    rw [← Real.exp_add] at hh'
    have hh'' : Real.exp (x ^ 2 / 4 + -x ^ 2 / 4) = 1 := by ring_nf; exact Real.exp_zero
    rw [hh''] at hh'
    nlinarith
  have hxp : |x| * ((m : ℝ) * standardNormalPDF x) ≤ 2 * standardNormalPDF 0 := by
    rw [abs_of_nonneg hx]
    have hh := (mul_le_mul_of_nonneg_left he hx).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hxexp hp0] :
        x * (standardNormalPDF 0 * Real.exp (-x ^ 2 / 4)) ≤ 2 * standardNormalPDF 0)
    exact hh
  exact (normalMaximumDensity_derivative_abs_le hm x).trans (by
    have hh := pow_le_pow_left₀ (mul_nonneg hm0.le hp) hmp 2
    nlinarith)

def gaussianMaximumCurvatureConstant : ℝ :=
  (9 * standardNormalPDF 0 ^ 2 + 3 * standardNormalPDF 0) +
  (16 * (standardNormalPDF 0 / standardNormalUpperTail 0) ^ 2 +
    2 * (standardNormalPDF 0 / standardNormalUpperTail 0)) +
  (standardNormalPDF 0 ^ 2 + 2 * standardNormalPDF 0) +
  9 * (16 * gaussianMillsUniformConstant ^ 2 + 2 * gaussianMillsUniformConstant)

theorem gaussianMaximumCurvatureConstant_pos : 0 < gaussianMaximumCurvatureConstant := by
  have := standardNormalPDF_pos 0
  have := standardNormalUpperTail_pos 0
  have := gaussianMillsUniformConstant_pos
  unfold gaussianMaximumCurvatureConstant
  positivity

/-- The printed global Gaussian maximum smoothness display, for all
thresholds and every `m ≥ 2`, obtained by its negative, central-positive,
and far-positive region estimates (with `m=2,3` treated separately). -/
theorem normalMaximumDensity_derivative_global_bound {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    |deriv (normalMaximumDensity m) x| ≤
      gaussianMaximumCurvatureConstant * dimensionLog m := by
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one (by omega)
  have hL0 : 0 ≤ dimensionLog m := by linarith
  have hp0 := (standardNormalPDF_pos 0).le
  have hq0 := standardNormalUpperTail_pos 0
  have hC := gaussianMillsUniformConstant_pos.le
  have hr : 0 ≤ standardNormalPDF 0 / standardNormalUpperTail 0 := by positivity
  have hK : 0 ≤ 16 * gaussianMillsUniformConstant ^ 2 + 2 * gaussianMillsUniformConstant := by positivity
  have hsmall : 9 * standardNormalPDF 0 ^ 2 + 3 * standardNormalPDF 0 ≤
      gaussianMaximumCurvatureConstant := by
    unfold gaussianMaximumCurvatureConstant
    nlinarith [sq_nonneg (standardNormalPDF 0 / standardNormalUpperTail 0),
      sq_nonneg (standardNormalPDF 0), sq_nonneg gaussianMillsUniformConstant]
  have hnegative : 16 * (standardNormalPDF 0 / standardNormalUpperTail 0) ^ 2 +
      2 * (standardNormalPDF 0 / standardNormalUpperTail 0) ≤
      gaussianMaximumCurvatureConstant := by
    unfold gaussianMaximumCurvatureConstant
    nlinarith [sq_nonneg (standardNormalPDF 0), sq_nonneg gaussianMillsUniformConstant]
  have hfar : standardNormalPDF 0 ^ 2 + 2 * standardNormalPDF 0 ≤
      gaussianMaximumCurvatureConstant := by
    unfold gaussianMaximumCurvatureConstant
    nlinarith [sq_nonneg (standardNormalPDF 0 / standardNormalUpperTail 0),
      sq_nonneg (standardNormalPDF 0), sq_nonneg gaussianMillsUniformConstant]
  have hcentral : 9 * (16 * gaussianMillsUniformConstant ^ 2 + 2 * gaussianMillsUniformConstant) ≤
      gaussianMaximumCurvatureConstant := by
    unfold gaussianMaximumCurvatureConstant
    nlinarith [sq_nonneg (standardNormalPDF 0 / standardNormalUpperTail 0),
      sq_nonneg (standardNormalPDF 0)]
  have hscale : gaussianMaximumCurvatureConstant ≤
      gaussianMaximumCurvatureConstant * dimensionLog m :=
    le_mul_of_one_le_right gaussianMaximumCurvatureConstant_pos.le hL
  by_cases hm3 : m ≤ 3
  · exact (normalMaximumDensity_derivative_small_dimension hm hm3 x).trans (hsmall.trans hscale)
  have hm4 : 4 ≤ m := by omega
  by_cases hx : x ≤ 0
  · exact (normalMaximumDensity_derivative_negative_region hm4 hx).trans (hnegative.trans hscale)
  have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
  by_cases hxc : x ≤ 2 * Real.sqrt (dimensionLog m)
  · have hs0 := Real.sqrt_nonneg (dimensionLog m)
    have hs2 := Real.sq_sqrt hL0
    have hs1 : 1 ≤ Real.sqrt (dimensionLog m) := by nlinarith
    have hb : (1 + x) ^ 2 ≤ 9 * dimensionLog m := by
      have hh : 1 + x ≤ 3 * Real.sqrt (dimensionLog m) := by linarith
      nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x) hh 2]
    exact (normalMaximumDensity_derivative_positive_region hm4 hx0).trans
      ((mul_le_mul_of_nonneg_left hb hK).trans (by nlinarith [mul_le_mul_of_nonneg_right hcentral hL0]))
  · have hxlarge : 2 * Real.sqrt (dimensionLog m) ≤ x := le_of_not_ge hxc
    have hxsq : 4 * dimensionLog m ≤ x ^ 2 := by
      nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg (dimensionLog m),
        pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.sqrt (dimensionLog m)) hxlarge 2]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have heL : dimensionLog m = 1 + Real.log (m : ℝ) := by
      rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hm0.ne', Real.log_exp]
    exact (normalMaximumDensity_derivative_far_positive hm hx0 (by rw [heL] at hxsq; linarith)).trans
      (hfar.trans hscale)

theorem normalMaximumCDF_second_derivative_global_bound {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    |deriv (deriv (normalMaximumCDF m)) x| ≤
      gaussianMaximumCurvatureConstant * dimensionLog m := by
  have hd : deriv (normalMaximumCDF m) = normalMaximumDensity m :=
    funext (fun y => (hasDerivAt_normalMaximumCDF m y).deriv)
  rw [hd]
  exact normalMaximumDensity_derivative_global_bound hm x

end
end RectangleCLT.Companion.SplitV4.Printed

import RectangleCLTCompanion.LowerSkewTail
import RectangleCLTCompanion.LowerMaxCDFActual

/-!
# A nonvanishing skewed discrepancy at every positive critical scale

The skewness coefficient need not converge. Its uniform positive lower
bound and the actual Cramér estimate give a fixed detecting error.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def lowerCriticalLogGain (r : ℝ) : ℝ := Real.sqrt 2 * r / 32

def lowerCriticalError (r : ℝ) : ℝ :=
  (Real.exp (-1) - Real.exp (-Real.exp (lowerCriticalLogGain r))) / 2

lemma lowerCriticalLogGain_pos {r : ℝ} (hr : 0 < r) : 0 < lowerCriticalLogGain r := by
  unfold lowerCriticalLogGain
  positivity

lemma lowerCriticalError_pos {r : ℝ} (hr : 0 < r) : 0 < lowerCriticalError r := by
  unfold lowerCriticalError
  apply half_pos
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  have he : 1 < Real.exp (lowerCriticalLogGain r) := Real.one_lt_exp_iff.mpr (lowerCriticalLogGain_pos hr)
  linarith

lemma lowerCritical_tail_ratio_eventually_ge
    {B : ℕ → ℝ} {p : ℕ → ℕ} {r : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop) (hrpos : 0 < r)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r)) :
    ∀ᶠ n in atTop, Real.exp (lowerCriticalLogGain r) ≤
      lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) /
        standardNormalUpperTail (normalMaxThreshold (p n)) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hnorm := lowerSkew_log_tail_normalized hB hp hr
  filter_upwards [hnorm.eventually (eventually_gt_nhds (by linarith : -Real.sqrt (2 : ℝ)/8 < 0)),
    hr.eventually (eventually_gt_nhds (half_lt_self hrpos)), lowerSkewRate_eventually_pos hB hp,
    lowerSkew_cramer_eventually hB hp hr] with n hn hnr hrate hactual
  have hcoef := (lowerSkewCoefficient_bounds (hB n)).1
  have hratio : Real.sqrt 2 / 8 ≤
      lowerSkewLogTail (B n) (p n) n / lowerSkewRate (B n) (p n) n := by linarith
  have hleading := (le_div_iff₀ hrate).mp hratio
  have hgain : lowerCriticalLogGain r ≤ lowerSkewLogTail (B n) (p n) n := by
    unfold lowerCriticalLogGain
    nlinarith
  have hq : 0 < lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) /
      standardNormalUpperTail (normalMaxThreshold (p n)) :=
    div_pos hactual.1 (standardNormalUpperTail_pos _)
  have he := Real.exp_le_exp.mpr hgain
  simpa only [lowerSkewLogTail, Real.exp_log hq] using he

lemma lowerMaximum_rectangleError_ge_comparator
    {B c : ℝ} {n d P : ℕ} (hd : 1 ≤ d) (hdP : d ≤ P)
    (hcomp : c ≤ lowerCoordinateUpperTail B n (normalMaxThreshold d) /
      standardNormalUpperTail (normalMaxThreshold d)) :
    Real.exp (-1) - (1-c*standardNormalUpperTail (normalMaxThreshold d))^d ≤
      rectangleError (lowerArrayLaw B n P)
        (sumVector (lowerNormalizedRows (n := n) (p := P))) 1
        (partialMaximumRectangle P d (normalMaxThreshold d)) := by
  have ht := (le_div_iff₀ (standardNormalUpperTail_pos (normalMaxThreshold d))).mp hcomp
  have hCDF : lowerCoordinateCDF B n (normalMaxThreshold d) ≤
      1-c*standardNormalUpperTail (normalMaxThreshold d) := by
    rw [lowerCoordinateCDF_eq_one_sub_upperTail]
    linarith
  have hCDF0 : 0 ≤ lowerCoordinateCDF B n (normalMaxThreshold d) := measureReal_nonneg
  have hpow := pow_le_pow_left₀ hCDF0 hCDF d
  rw [lowerArrayLaw_partialMaximum_rectangleError B n hdP,
    ← lowerCoordinateCDF_eq_one_sub_upperTail, standardNormalCDF_normalMaxThreshold_pow hd,
    abs_sub_comm]
  exact (sub_le_sub_left hpow _).trans (le_abs_self _)

/-- A fixed positive critical rate prevents convergence uniformly over
all larger ambient dimensions, without any limit on the skewness ratio. -/
theorem lowerCritical_rectangleError_eventually_ge
    {B : ℕ → ℝ} {p : ℕ → ℕ} {r : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop) (hrpos : 0 < r)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r)) :
    ∀ᶠ n in atTop, ∀ P : ℕ, p n ≤ P →
      lowerCriticalError r ≤ rectangleError (lowerArrayLaw (B n) n P)
        (sumVector (lowerNormalizedRows (n := n) (p := P))) 1
        (partialMaximumRectangle P (p n) (normalMaxThreshold (p n))) := by
  let c := Real.exp (lowerCriticalLogGain r)
  have hratio : Tendsto (fun n =>
      (c*standardNormalUpperTail (normalMaxThreshold (p n))) /
        standardNormalUpperTail (normalMaxThreshold (p n))) atTop (𝓝 c) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)) using 1
    funext n
    field_simp [(standardNormalUpperTail_pos (normalMaxThreshold (p n))).ne']
  have hmax := tendsto_maximum_CDF_of_normal_tail_ratio hp hratio
  have hgap := (tendsto_const_nhds (x := Real.exp (-1))).sub hmax
  have hgap' : Tendsto (fun n => Real.exp (-1) -
      (1-c*standardNormalUpperTail (normalMaxThreshold (p n)))^(p n))
      atTop (𝓝 (2*lowerCriticalError r)) := by
    convert hgap using 1
    unfold lowerCriticalError c
    ring
  have hevent := hgap'.eventually (eventually_gt_nhds
    (by linarith [lowerCriticalError_pos hrpos] : lowerCriticalError r < 2*lowerCriticalError r))
  filter_upwards [hevent, lowerCritical_tail_ratio_eventually_ge hB hp hrpos hr,
    hp.eventually (eventually_ge_atTop 1)] with n hn hcomp hpn P hpP
  exact hn.le.trans (lowerMaximum_rectangleError_ge_comparator hpn hpP hcomp)

end

end RectangleCLT.Companion

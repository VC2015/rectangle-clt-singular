import RectangleCLTCompanion.RademacherTilt
import RectangleCLTCompanion.NormalQuantileRate
import RectangleCLTCompanion.LowerTiltedArray

/-! # Rademacher parameters at the critical rectangle dimension -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def rademacherCriticalU (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  normalMaxThreshold (p n) / Real.sqrt n

def rademacherCriticalTilt (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  rademacherTiltParameter (rademacherCriticalU p n)

def rademacherCriticalScale (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  rademacherCriticalTilt p n * Real.sqrt n *
    Real.sqrt (lowerTiltVariance 1 (rademacherCriticalTilt p n))

lemma rademacher_sqrt_nat_atTop :
    Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
  simpa only [Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop

lemma criticalDimension_tendsto {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto p atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (p n : ℝ)) atTop atTop := by
    apply (rademacher_sqrt_nat_atTop.atTop_mul_pos ha hcrit).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
    field_simp
  have hcast : Tendsto (fun n : ℕ => (p n : ℝ)) atTop atTop := by
    apply (Real.tendsto_exp_atTop.comp hlog).congr'
    filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with n hn
    have hp0 : p n ≠ 0 := by intro hz; simp [hz] at hn
    change Real.exp (Real.log (p n : ℝ)) = (p n : ℝ)
    exact Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hp0)
  exact tendsto_natCast_atTop_iff.mp hcast

lemma rademacherCriticalU_eventually_pos {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    ∀ᶠ n in atTop, 0 < rademacherCriticalU p n := by
  have hx := tendsto_normalMaxThreshold_atTop.comp (criticalDimension_tendsto ha hcrit)
  filter_upwards [hx.eventually (eventually_gt_atTop 0), eventually_ge_atTop 1] with n hx hn
  exact div_pos hx (Real.sqrt_pos.2 (by exact_mod_cast hn))

lemma tendsto_rademacherCriticalU_sq {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n => (rademacherCriticalU p n)^2) atTop (𝓝 0) := by
  have hp := criticalDimension_tendsto ha hcrit
  have hx := tendsto_normalMaxThreshold_sq_div_log.comp hp
  have hh := (hx.mul hcrit).div_atTop rademacher_sqrt_nat_atTop
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hp2 hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hl : Real.log (p n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp2))
  simp only [Function.comp_def, rademacherCriticalU]
  field_simp [hs, hl]

lemma tendsto_rademacherCriticalU {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (rademacherCriticalU p) atTop (𝓝 0) := by
  have hh := Real.continuous_sqrt.tendsto 0 |>.comp (tendsto_rademacherCriticalU_sq ha hcrit)
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [rademacherCriticalU_eventually_pos ha hcrit] with n hn
  simp only [Function.comp_def]
  rw [Real.sqrt_sq hn.le]

lemma tendsto_rademacherCriticalU_fourth {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (rademacherCriticalU p n)^4) atTop (𝓝 (4*a^2)) := by
  have hp := criticalDimension_tendsto ha hcrit
  have hx := tendsto_normalMaxThreshold_sq_div_log.comp hp
  have hh := (hx.mul hcrit).pow 2
  have hh' : Tendsto (fun n : ℕ =>
      ((normalMaxThreshold (p n))^2 / Real.log (p n : ℝ) *
        (Real.log (p n : ℝ) / Real.sqrt n))^2) atTop (𝓝 (4*a^2)) := by
    convert hh using 1 <;> ring
  apply hh'.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hp2 hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hl : Real.log (p n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp2))
  unfold rademacherCriticalU
  field_simp [hs, hl]
  have hs4 : Real.sqrt (n : ℝ)^4 = (n : ℝ)^2 := by
    rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hs4]
  ring

lemma rademacherCriticalU_eventually_mem {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    ∀ᶠ n in atTop, rademacherCriticalU p n ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [rademacherCriticalU_eventually_pos ha hcrit,
    (tendsto_rademacherCriticalU ha hcrit).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn0 hn1
  exact ⟨hn0, hn1⟩

lemma tendsto_rademacherCriticalU_right {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (rademacherCriticalU p) atTop (𝓝[>] 0) := by
  exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_rademacherCriticalU ha hcrit,
    rademacherCriticalU_eventually_pos ha hcrit⟩

lemma tendsto_rademacherCritical_exponent {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (normalMaxThreshold (p n))^2/2 -
      (n : ℝ)*rademacherRateFunction (rademacherCriticalU p n))
      atTop (𝓝 (-a^2/3)) := by
  have hrate := tendsto_rademacherRateFunction_fourth.comp (tendsto_rademacherCriticalU_right ha hcrit)
  have hfour := tendsto_rademacherCriticalU_fourth ha hcrit
  have hh := (hrate.mul hfour).neg
  have hh' : Tendsto (fun n : ℕ =>
      -((rademacherRateFunction (rademacherCriticalU p n) - (rademacherCriticalU p n)^2/2) /
        (rademacherCriticalU p n)^4 * ((n : ℝ)*(rademacherCriticalU p n)^4)))
      atTop (𝓝 (-a^2/3)) := by convert hh using 1 <;> ring
  apply hh'.congr'
  filter_upwards [rademacherCriticalU_eventually_pos ha hcrit, eventually_ge_atTop 1] with n hu hn
  have hu0 := ne_of_gt hu
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  field_simp [hu0]
  unfold rademacherCriticalU
  field_simp [hs]
  nlinarith [hsq]

lemma tendsto_rademacherCriticalTilt {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (rademacherCriticalTilt p) atTop (𝓝 0) := by
  have hh := (hasDerivAt_rademacherTiltParameter (u := 0) (by constructor <;> norm_num)).continuousAt.tendsto.comp
    (tendsto_rademacherCriticalU ha hcrit)
  simpa only [rademacherTiltParameter_zero] using hh

lemma tendsto_rademacherCriticalVariance {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n => lowerTiltVariance 1 (rademacherCriticalTilt p n)) atTop (𝓝 1) := by
  have hh : Tendsto (fun n => (1 : ℝ) - (rademacherCriticalU p n)^2) atTop (𝓝 (1-0)) :=
    tendsto_const_nhds.sub (tendsto_rademacherCriticalU_sq ha hcrit)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [rademacherCriticalU_eventually_mem ha hcrit] with n hn
  exact (lowerTiltVariance_rademacher ⟨by linarith [hn.1], hn.2⟩).symm

lemma tendsto_rademacherCriticalScale_div_threshold {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n => rademacherCriticalScale p n / normalMaxThreshold (p n)) atTop (𝓝 1) := by
  have ht := tendsto_rademacherTiltParameter_div.comp (tendsto_rademacherCriticalU_right ha hcrit)
  have hv := Real.continuous_sqrt.tendsto 1 |>.comp (tendsto_rademacherCriticalVariance ha hcrit)
  simp only [Real.sqrt_one] at hv
  have hh := ht.mul hv
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [rademacherCriticalU_eventually_pos ha hcrit, eventually_ge_atTop 1] with n hu hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hx : normalMaxThreshold (p n) ≠ 0 := by
    intro hx
    simp [rademacherCriticalU, hx] at hu
  simp only [Function.comp_def, rademacherCriticalScale, rademacherCriticalTilt, rademacherCriticalU]
  field_simp

lemma tendsto_rademacherCriticalScale_atTop {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (rademacherCriticalScale p) atTop atTop := by
  have hx := tendsto_normalMaxThreshold_atTop.comp (criticalDimension_tendsto ha hcrit)
  have hh := hx.atTop_mul_pos (by norm_num : (0 : ℝ) < 1)
    (tendsto_rademacherCriticalScale_div_threshold ha hcrit)
  apply hh.congr'
  filter_upwards [hx.eventually (eventually_gt_atTop 0)] with n hn
  simp only [Function.comp_def] at hn ⊢
  field_simp [ne_of_gt hn]

lemma tendsto_rademacherCritical_tilted_error_scale {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n => (lowerTiltedNormalization 1 (rademacherCriticalTilt p n) n * (2*1)) *
      rademacherCriticalScale p n) atTop (𝓝 0) := by
  have hh := (tendsto_rademacherCriticalTilt ha hcrit).const_mul (2 : ℝ)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hv : Real.sqrt (lowerTiltVariance 1 (rademacherCriticalTilt p n)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (lowerTiltVariance_pos (by norm_num : (0 : ℝ) < 1) _)
  unfold lowerTiltedNormalization rademacherCriticalScale
  field_simp
  ring

end

end RectangleCLT.Companion

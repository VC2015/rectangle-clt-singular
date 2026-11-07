import RectangleCLTCompanion.NormalQuantileRate
import RectangleCLT.GaussianProjectionMaximum

/-! Extreme-value calibration from the actual standard normal law.
All distributional functions below are powers of the genuine normal CDF. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def normalMaximumCDF (m : ℕ) (t : ℝ) : ℝ := standardNormalCDF t ^ m

def normalMaximumDensity (m : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * standardNormalCDF t ^ (m-1) * standardNormalPDF t

theorem hasDerivAt_normalMaximumCDF (m : ℕ) (t : ℝ) :
    HasDerivAt (normalMaximumCDF m) (normalMaximumDensity m t) t := by
  simpa only [normalMaximumCDF, normalMaximumDensity] using (hasDerivAt_standardNormalCDF t).pow m

theorem normal_mills_density_ratio_bounds {x : ℝ} (hx : 0 < x) :
    1 ≤ standardNormalPDF x / (x * standardNormalUpperTail x) ∧
    standardNormalPDF x / (x * standardNormalUpperTail x) ≤ 1 + 1/x^2 := by
  have ht := standardNormalUpperTail_pos x
  have hp : 0 < x*standardNormalUpperTail x := mul_pos hx ht
  have hlo := (le_div_iff₀ hx).mp (standardNormalUpperTail_le_mills hx)
  have hhi := (div_le_iff₀ (by positivity : 0 < x^2+1)).mp (mills_le_standardNormalUpperTail hx)
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith only [hlo]
  · apply (div_le_iff₀ hp).mpr
    have hid : (1+1/x^2)*(x*standardNormalUpperTail x)*x =
        standardNormalUpperTail x*(x^2+1) := by field_simp; ring
    apply (mul_le_mul_right hx).mp
    rw [hid]
    exact hhi

theorem tendsto_normal_mills_density_ratio :
    Tendsto (fun x : ℝ => standardNormalPDF x / (x * standardNormalUpperTail x))
      atTop (𝓝 1) := by
  have hz : Tendsto (fun x : ℝ => 1/x^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have hu : Tendsto (fun x : ℝ => 1+1/x^2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (normal_mills_density_ratio_bounds hx).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (normal_mills_density_ratio_bounds hx).2

theorem tendsto_normalMax_mills_calibration :
    Tendsto (fun m : ℕ => (m : ℝ)*standardNormalPDF (normalMaxThreshold m) /
      normalMaxThreshold m) atTop (𝓝 1) := by
  have hh := tendsto_mul_standardNormalUpperTail_normalMaxThreshold.mul
    (tendsto_normal_mills_density_ratio.comp tendsto_normalMaxThreshold_atTop)
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [tendsto_normalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
  field_simp [ne_of_gt (standardNormalUpperTail_pos (normalMaxThreshold m)), ne_of_gt hm]
  ring

theorem tendsto_normalMax_cdf_pred_power :
    Tendsto (fun m : ℕ => standardNormalCDF (normalMaxThreshold m) ^ (m-1))
      atTop (𝓝 (Real.exp (-1))) := by
  have hh := (tendsto_const_nhds (x := Real.exp (-1))).div tendsto_standardNormalCDF_normalMaxThreshold
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  dsimp only [Pi.div_apply]
  symm
  apply (eq_div_iff (ne_of_gt (standardNormalCDF_pos _))).mpr
  rw [← pow_succ, Nat.sub_add_cancel hm, standardNormalCDF_normalMaxThreshold_pow hm]

theorem tendsto_normalMaximumDensity_at_threshold_div_sqrt_log :
    Tendsto (fun m : ℕ => normalMaximumDensity m (normalMaxThreshold m) /
      Real.sqrt (2*Real.log (m : ℝ))) atTop (𝓝 (Real.exp (-1))) := by
  have hh := (tendsto_normalMax_mills_calibration.mul tendsto_normalMax_cdf_pred_power).mul
    tendsto_normalMaxThreshold_div_sqrt_two_log
  simp only [one_mul, mul_one] at hh
  apply hh.congr'
  filter_upwards [tendsto_normalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
  dsimp [normalMaximumDensity]
  field_simp [ne_of_gt hm]
  ring

/-- The genuine derivative of the maximum density, including the negative
Gaussian-score term. -/
theorem hasDerivAt_normalMaximumDensity {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    HasDerivAt (normalMaximumDensity m)
      ((m : ℝ)*(m-1)*standardNormalCDF t^(m-2)*standardNormalPDF t^2 -
        t*normalMaximumDensity m t) t := by
  have hh := (((hasDerivAt_standardNormalCDF t).pow (m-1)).const_mul (m : ℝ)).mul
    (hasDerivAt_standardNormalPDF t)
  have hpred : m-1-1 = m-2 := by omega
  have heq : (fun y => (m : ℝ)*standardNormalCDF y^(m-1)*standardNormalPDF y) = normalMaximumDensity m := rfl
  rw [heq] at hh
  convert hh using 1
  rw [hpred, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  dsimp [normalMaximumDensity]
  ring

theorem normalMaximumDensity_derivative_abs_le {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    |deriv (normalMaximumDensity m) t| ≤
      ((m : ℝ)*standardNormalPDF t)^2 + |t| *((m : ℝ)*standardNormalPDF t) := by
  rw [(hasDerivAt_normalMaximumDensity hm t).deriv]
  have hp := (standardNormalPDF_pos t).le
  have hc := standardNormalCDF_nonneg t
  have hc1 := standardNormalCDF_le_one t
  have hpow (k : ℕ) : 0 ≤ standardNormalCDF t^k ∧ standardNormalCDF t^k ≤ 1 :=
    ⟨pow_nonneg hc k, pow_le_one₀ hc hc1⟩
  have hm0 : (0 : ℝ) ≤ m-1 := by
    have hh : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  have hm1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hfirst : 0 ≤ (m : ℝ)*(m-1)*standardNormalCDF t^(m-2)*standardNormalPDF t^2 := by positivity
  have hfirstle : (m : ℝ)*(m-1)*standardNormalCDF t^(m-2)*standardNormalPDF t^2 ≤
      ((m : ℝ)*standardNormalPDF t)^2 := by
    have hh := mul_le_mul_of_nonneg_left (hpow (m-2)).2
      (mul_nonneg (mul_nonneg hm1 hm0) (sq_nonneg (standardNormalPDF t)))
    nlinarith [sq_nonneg (standardNormalPDF t), mul_nonneg hm1 (sq_nonneg (standardNormalPDF t))]
  have hD : |normalMaximumDensity m t| ≤ (m : ℝ)*standardNormalPDF t := by
    dsimp [normalMaximumDensity]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (hpow (m-1)).2 (mul_nonneg hm1 hp)]
  calc
    _ ≤ |(m : ℝ)*(m-1)*standardNormalCDF t^(m-2)*standardNormalPDF t^2| +
        |t*normalMaximumDensity m t| := abs_sub _ _
    _ = (m : ℝ)*(m-1)*standardNormalCDF t^(m-2)*standardNormalPDF t^2 +
        |t| *|normalMaximumDensity m t| := by rw [abs_of_nonneg hfirst, abs_mul]
    _ ≤ _ := add_le_add hfirstle (mul_le_mul_of_nonneg_left hD (abs_nonneg t))

theorem standardNormalPDF_shift_bound (u t : ℝ) :
    standardNormalPDF t = standardNormalPDF u * Real.exp ((u^2-t^2)/2) := by
  rw [standardNormalPDF_eq, standardNormalPDF_eq, mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem local_normalPDF_bound {u t L : ℝ} (hL : 1 ≤ L) (hu0 : 0 ≤ u)
    (hu : u ≤ 2*Real.sqrt L) (ht : |t-u| ≤ 1/Real.sqrt L) :
    standardNormalPDF t ≤ standardNormalPDF u * Real.exp 3 ∧ |t| ≤ 3*Real.sqrt L := by
  let s := Real.sqrt L
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr hL
  have hs0 : 0 < s := by linarith
  have hts : |t-u| *s ≤ 1 := (le_div_iff₀ hs0).mp ht
  have htm : |t-u| ≤ 1 := ht.trans ((div_le_one hs0).mpr hs)
  have ht1 : |t| ≤ |t-u|+u := by
    simpa [abs_of_nonneg hu0] using abs_add (t-u) u
  constructor
  · rw [standardNormalPDF_shift_bound u t]
    apply mul_le_mul_of_nonneg_left _ (standardNormalPDF_nonneg u)
    apply Real.exp_le_exp.mpr
    have hlow : -|t-u| ≤ t-u := neg_abs_le (t-u)
    have hhigh : t-u ≤ |t-u| := le_abs_self (t-u)
    have hus : u*|t-u| ≤ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hu (abs_nonneg (t-u))]
    have hh : u^2-t^2 ≤ 2*u*|t-u| := by
      nlinarith [sq_nonneg (t-u), mul_le_mul_of_nonneg_left hlow hu0]
    nlinarith
  · dsimp [s] at hs
    nlinarith

/-- Only a neighborhood of the extreme-value threshold is required for the
signed-shift comparison; its density derivative is uniformly O(log m). -/
theorem eventually_normalMaximumDensity_local_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ t : ℝ,
      |t-normalMaxThreshold m| ≤ 1/Real.sqrt (Real.log (m : ℝ)) →
      |deriv (normalMaximumDensity m) t| ≤ C*Real.log (m : ℝ) := by
  let A : ℝ := 4*Real.exp 3
  refine ⟨A^2+3*A, by dsimp [A]; positivity, ?_⟩
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop 1),
    tendsto_normalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_normalMaxThreshold_sq_div_log.eventually (eventually_lt_nhds (by norm_num : (2 : ℝ) < 4)),
    tendsto_normalMax_mills_calibration.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))]
    with m hm hL hu hsq hpdf
  intro t ht
  let L := Real.log (m : ℝ)
  let u := normalMaxThreshold m
  let s := Real.sqrt L
  have hLp : 0 < L := by dsimp [L]; linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = L := Real.sq_sqrt hLp.le
  have hu2 : u^2 < 4*L := (div_lt_iff₀ hLp).mp hsq
  have hus : u ≤ 2*s := by nlinarith [hu.le]
  have hmpdf : (m : ℝ)*standardNormalPDF u ≤ 4*s := by
    have hh : (m : ℝ)*standardNormalPDF u < 2*u := (div_lt_iff₀ hu).mp hpdf
    linarith
  obtain ⟨hpt, htt⟩ := local_normalPDF_bound hL hu.le hus ht
  have hpt' : (m : ℝ)*standardNormalPDF t ≤ A*s := by
    have hh := mul_le_mul_of_nonneg_left hpt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hh' := mul_le_mul_of_nonneg_right hmpdf (Real.exp_nonneg 3)
    dsimp [A]
    nlinarith
  have hn : 0 ≤ (m : ℝ)*standardNormalPDF t := mul_nonneg (Nat.cast_nonneg m) (standardNormalPDF_nonneg t)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ((m : ℝ)*standardNormalPDF t)^2 + |t| *((m : ℝ)*standardNormalPDF t) :=
      normalMaximumDensity_derivative_abs_le hm t
    _ ≤ (A*s)^2 + (3*s)*(A*s) := add_le_add
      (pow_le_pow_left₀ hn hpt' 2)
      (mul_le_mul htt hpt' hn (by positivity))
    _ = (A^2+3*A)*Real.log (m : ℝ) := by change _ = (A^2+3*A)*L; nlinarith [hs2]

theorem tendsto_log_normalTail_below_max_threshold {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℕ => Real.log (standardNormalUpperTail (a*normalMaxThreshold m)) /
      Real.log (m : ℝ)) atTop (𝓝 (-a^2)) := by
  have hs : Tendsto (fun m : ℕ => a*normalMaxThreshold m) atTop atTop :=
    tendsto_const_nhds.pos_mul_atTop ha tendsto_normalMaxThreshold_atTop
  have h₁ := tendsto_log_standardNormalUpperTail_div_sq.comp hs
  have h₂ := tendsto_normalMaxThreshold_sq_div_log.const_mul (a^2)
  have hh := h₁.mul h₂
  have hh' : Tendsto (fun m : ℕ =>
      (Real.log (standardNormalUpperTail (a*normalMaxThreshold m)) / (a*normalMaxThreshold m)^2) *
        (a^2*((normalMaxThreshold m)^2/Real.log (m : ℝ)))) atTop (𝓝 (-a^2)) := by
    convert hh using 1 <;> ring
  apply hh'.congr'
  filter_upwards [tendsto_normalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop 2] with m hm hm2
  have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  field_simp [ne_of_gt ha, ne_of_gt hm, hl]
  ring

theorem tendsto_normalTail_mass_below_max_threshold {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun m : ℕ => (m : ℝ)*standardNormalUpperTail (a*normalMaxThreshold m)) atTop atTop := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_log_normalTail_below_max_threshold ha)
  have hr' : Tendsto (fun m : ℕ => Real.log ((m : ℝ)*standardNormalUpperTail (a*normalMaxThreshold m)) /
      Real.log (m : ℝ)) atTop (𝓝 (1-a^2)) := by
    apply hr.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [Real.log_mul (ne_of_gt hmp) (ne_of_gt (standardNormalUpperTail_pos _))]
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  have hp : 0 < 1-a^2 := by nlinarith
  have hh := hlog.atTop_mul_pos hp hr'
  have hh' : Tendsto (fun m : ℕ => Real.log ((m : ℝ)*standardNormalUpperTail (a*normalMaxThreshold m))) atTop atTop := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  apply (Real.tendsto_exp_atTop.comp hh').congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact Real.exp_log (mul_pos (by exact_mod_cast (show 0 < m by omega)) (standardNormalUpperTail_pos _))

theorem normalMaximumCDF_le_exp_tail_mass (m : ℕ) (t : ℝ) :
    normalMaximumCDF m t ≤ Real.exp (-(m : ℝ)*standardNormalUpperTail t) := by
  have he : standardNormalCDF t ≤ Real.exp (-standardNormalUpperTail t) := by
    have hh := Real.add_one_le_exp (-standardNormalUpperTail t)
    rw [standardNormalUpperTail_eq_one_sub] at hh ⊢
    linarith
  have hh := pow_le_pow_left₀ (standardNormalCDF_nonneg t) he m
  rw [← Real.exp_nat_mul] at hh
  simpa [normalMaximumCDF, mul_neg, neg_mul] using hh

theorem tendsto_normalMaximumCDF_below_threshold {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun m : ℕ => normalMaximumCDF m (a*normalMaxThreshold m)) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_normalTail_mass_below_max_threshold ha ha1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · exact Eventually.of_forall (fun m => pow_nonneg (standardNormalCDF_nonneg _) m)
  · filter_upwards [] with m
    simpa [neg_mul] using normalMaximumCDF_le_exp_tail_mass m (a*normalMaxThreshold m)

end
end RectangleCLT.Companion.SplitV4

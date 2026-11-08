import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMoments

/-! The literal threshold in `sym:eq:gaussian-max`: `m * normalTail(u_m) = 1`.
This is added beside the earlier maximum-CDF quantile. Its Mills scale and
the density at this exact threshold are proved without substituting the
nearby CDF quantile for a printed equality. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem printedNormalMaxLevel_mem_Ioo {m : ℕ} (hm : 2 ≤ m) :
    1 - 1 / (m : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hi : 1 / (m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hmR
  constructor
  · linarith
  · linarith [one_div_pos.mpr hmp]

def printedNormalMaxThreshold (m : ℕ) : ℝ :=
  if hm : 2 ≤ m then
    Classical.choose (exists_standardNormalCDF_eq
      (printedNormalMaxLevel_mem_Ioo hm).1 (printedNormalMaxLevel_mem_Ioo hm).2)
  else 0

theorem standardNormalCDF_printedNormalMaxThreshold {m : ℕ} (hm : 2 ≤ m) :
    standardNormalCDF (printedNormalMaxThreshold m) = 1 - 1 / (m : ℝ) := by
  rw [printedNormalMaxThreshold, dif_pos hm]
  exact Classical.choose_spec (exists_standardNormalCDF_eq
    (printedNormalMaxLevel_mem_Ioo hm).1 (printedNormalMaxLevel_mem_Ioo hm).2)

theorem standardNormalUpperTail_printedNormalMaxThreshold {m : ℕ} (hm : 2 ≤ m) :
    standardNormalUpperTail (printedNormalMaxThreshold m) = 1 / (m : ℝ) := by
  rw [standardNormalUpperTail_eq_one_sub, standardNormalCDF_printedNormalMaxThreshold hm]
  ring

theorem printedNormalMaxThreshold_tail_identity {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) * standardNormalUpperTail (printedNormalMaxThreshold m) = 1 := by
  rw [standardNormalUpperTail_printedNormalMaxThreshold hm]
  field_simp

theorem tendsto_standardNormalCDF_printedNormalMaxThreshold :
    Tendsto (fun m : ℕ => standardNormalCDF (printedNormalMaxThreshold m)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  exact (standardNormalCDF_printedNormalMaxThreshold hm).symm

theorem tendsto_printedNormalMaxThreshold_atTop : Tendsto printedNormalMaxThreshold atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  filter_upwards [tendsto_standardNormalCDF_printedNormalMaxThreshold.eventually
    (eventually_gt_nhds (standardNormalCDF_lt_one r))] with m hm
  exact (strictMono_standardNormalCDF.lt_iff_lt.mp hm).le

theorem tendsto_mul_standardNormalUpperTail_printedNormalMaxThreshold :
    Tendsto (fun m : ℕ => (m : ℝ) * standardNormalUpperTail (printedNormalMaxThreshold m))
      atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  exact (printedNormalMaxThreshold_tail_identity hm).symm

lemma tendsto_log_printedNormalMaxTail_div_log :
    Tendsto (fun p : ℕ => Real.log (standardNormalUpperTail (printedNormalMaxThreshold p)) /
      Real.log (p : ℝ)) atTop (𝓝 (-1 : ℝ)) := by
  have hlogmul : Tendsto (fun p : ℕ => Real.log
      ((p : ℝ) * standardNormalUpperTail (printedNormalMaxThreshold p))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      tendsto_mul_standardNormalUpperTail_printedNormalMaxThreshold
  have hlogp : Tendsto (fun p : ℕ => Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (hlogmul.div_atTop hlogp).sub_const (1 : ℝ)
  simp only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp1)
  have hlog0 : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1)
  rw [Real.log_mul hp0 (ne_of_gt (standardNormalUpperTail_pos _))]
  field_simp

lemma tendsto_printedNormalMaxThreshold_sq_div_log :
    Tendsto (fun p : ℕ => (printedNormalMaxThreshold p)^2 / Real.log (p : ℝ))
      atTop (𝓝 (2 : ℝ)) := by
  have htail := tendsto_log_standardNormalUpperTail_div_sq.comp tendsto_printedNormalMaxThreshold_atTop
  have hlim := tendsto_log_printedNormalMaxTail_div_log.div htail (by norm_num : (-1/2 : ℝ) ≠ 0)
  have hlim' : Tendsto (fun p : ℕ =>
      (Real.log (standardNormalUpperTail (printedNormalMaxThreshold p)) / Real.log (p : ℝ)) /
      (Real.log (standardNormalUpperTail (printedNormalMaxThreshold p)) / (printedNormalMaxThreshold p)^2))
      atTop (𝓝 (2 : ℝ)) := by convert hlim using 1 <;> norm_num
  apply hlim'.congr'
  filter_upwards [tendsto_printedNormalMaxThreshold_atTop.eventually (eventually_gt_atTop 0),
    eventually_ge_atTop 2] with p hp hp2
  have hlog0 : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp2))
  have hx : printedNormalMaxThreshold p ≠ 0 := ne_of_gt hp
  have ht := log_standardNormalUpperTail_ne_zero (printedNormalMaxThreshold p)
  field_simp [ht, hx, hlog0]
  ring

lemma tendsto_printedNormalMaxThreshold_sq_div_two_log :
    Tendsto (fun p : ℕ => (printedNormalMaxThreshold p)^2 / (2 * Real.log (p : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have h := tendsto_printedNormalMaxThreshold_sq_div_log.div_const (2 : ℝ)
  convert h using 1
  · funext p
    rw [div_div, mul_comm]
  · norm_num

lemma tendsto_printedNormalMaxThreshold_div_sqrt_two_log :
    Tendsto (fun p : ℕ => printedNormalMaxThreshold p / Real.sqrt (2 * Real.log (p : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have h := Real.continuous_sqrt.tendsto 1 |>.comp tendsto_printedNormalMaxThreshold_sq_div_two_log
  have h' : Tendsto (fun p : ℕ => Real.sqrt
      ((printedNormalMaxThreshold p)^2 / (2 * Real.log (p : ℝ)))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.sqrt_one] using h
  apply h'.congr'
  filter_upwards [tendsto_printedNormalMaxThreshold_atTop.eventually (eventually_gt_atTop 0)] with p hp
  rw [Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq_eq_abs, abs_of_pos hp]


/-- At the literal threshold, Mills' density/tail ratio fixes the leading
factor in `m * phi(u_m)`. -/
theorem tendsto_printedNormalMax_mills_calibration :
    Tendsto (fun m : ℕ => (m : ℝ) * standardNormalPDF (printedNormalMaxThreshold m) /
      printedNormalMaxThreshold m) atTop (𝓝 1) := by
  have hh := tendsto_mul_standardNormalUpperTail_printedNormalMaxThreshold.mul
    (tendsto_normal_mills_density_ratio.comp tendsto_printedNormalMaxThreshold_atTop)
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [tendsto_printedNormalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
  field_simp [(standardNormalUpperTail_pos (printedNormalMaxThreshold m)).ne', hm.ne']
  ring

/-- The CDF power at the literal threshold tends to `exp(-1)`. -/
theorem tendsto_printedNormalMax_cdf_power :
    Tendsto (fun m : ℕ => standardNormalCDF (printedNormalMaxThreshold m) ^ m)
      atTop (𝓝 (Real.exp (-1))) := by
  have hi : Tendsto (fun m : ℕ => -((m : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_natCast_atTop_atTop).neg
  have hine : Tendsto (fun m : ℕ => -((m : ℝ)⁻¹)) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hi, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    simpa only [mem_compl_iff, mem_singleton_iff, neg_eq_zero, inv_eq_zero] using hm0
  have hd : HasDerivAt (fun t : ℝ => Real.log (t + 1)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).add_const 1).log (by norm_num)
  have hs := hd.tendsto_slope_zero.comp hine
  have hlog : Tendsto (fun m : ℕ => (m : ℝ) *
      Real.log (standardNormalCDF (printedNormalMaxThreshold m))) atTop (𝓝 (-1)) := by
    have hn := hs.neg
    apply hn.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    rw [standardNormalCDF_printedNormalMaxThreshold hm]
    simp only [Function.comp_def, zero_add, smul_eq_mul, inv_neg, inv_inv,
      Real.log_one, sub_zero, neg_mul, neg_neg, one_div]
    congr 2
    ring
  apply (Real.continuous_exp.tendsto (-1) |>.comp hlog).congr'
  filter_upwards [] with m
  change Real.exp ((m : ℝ) * Real.log (standardNormalCDF (printedNormalMaxThreshold m))) = _
  rw [Real.exp_nat_mul, Real.exp_log (standardNormalCDF_pos _)]

theorem tendsto_printedNormalMax_cdf_pred_power :
    Tendsto (fun m : ℕ => standardNormalCDF (printedNormalMaxThreshold m) ^ (m - 1))
      atTop (𝓝 (Real.exp (-1))) := by
  have hh := tendsto_printedNormalMax_cdf_power.div
    tendsto_standardNormalCDF_printedNormalMaxThreshold (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  symm
  apply (eq_div_iff (standardNormalCDF_pos _).ne').mpr
  rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]

/-- The density asymptotic at the paper's exact `m*tail=1` threshold. -/
theorem tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log :
    Tendsto (fun m : ℕ => normalMaximumDensity m (printedNormalMaxThreshold m) /
      Real.sqrt (2 * Real.log (m : ℝ))) atTop (𝓝 (Real.exp (-1))) := by
  have hh := (tendsto_printedNormalMax_mills_calibration.mul tendsto_printedNormalMax_cdf_pred_power).mul
    tendsto_printedNormalMaxThreshold_div_sqrt_two_log
  simp only [one_mul, mul_one] at hh
  apply hh.congr'
  filter_upwards [tendsto_printedNormalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
  dsimp [normalMaximumDensity]
  field_simp [hm.ne']
  ring


theorem tendsto_log_normalTail_below_printed_max_threshold {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℕ => Real.log (standardNormalUpperTail (a*printedNormalMaxThreshold m)) /
      Real.log (m : ℝ)) atTop (𝓝 (-a^2)) := by
  have hs : Tendsto (fun m : ℕ => a*printedNormalMaxThreshold m) atTop atTop :=
    tendsto_const_nhds.pos_mul_atTop ha tendsto_printedNormalMaxThreshold_atTop
  have h₁ := tendsto_log_standardNormalUpperTail_div_sq.comp hs
  have h₂ := tendsto_printedNormalMaxThreshold_sq_div_log.const_mul (a^2)
  have hh := h₁.mul h₂
  have hh' : Tendsto (fun m : ℕ =>
      (Real.log (standardNormalUpperTail (a*printedNormalMaxThreshold m)) / (a*printedNormalMaxThreshold m)^2) *
        (a^2*((printedNormalMaxThreshold m)^2/Real.log (m : ℝ)))) atTop (𝓝 (-a^2)) := by
    convert hh using 1 <;> ring
  apply hh'.congr'
  filter_upwards [tendsto_printedNormalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop 2] with m hm hm2
  have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  field_simp [ne_of_gt ha, ne_of_gt hm, hl]
  ring

theorem tendsto_normalTail_mass_below_printed_max_threshold {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun m : ℕ => (m : ℝ)*standardNormalUpperTail (a*printedNormalMaxThreshold m)) atTop atTop := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_log_normalTail_below_printed_max_threshold ha)
  have hr' : Tendsto (fun m : ℕ => Real.log ((m : ℝ)*standardNormalUpperTail (a*printedNormalMaxThreshold m)) /
      Real.log (m : ℝ)) atTop (𝓝 (1-a^2)) := by
    apply hr.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [Real.log_mul (ne_of_gt hmp) (ne_of_gt (standardNormalUpperTail_pos _))]
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  have hp : 0 < 1-a^2 := by nlinarith
  have hh := hlog.atTop_mul_pos hp hr'
  have hh' : Tendsto (fun m : ℕ => Real.log ((m : ℝ)*standardNormalUpperTail (a*printedNormalMaxThreshold m))) atTop atTop := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  apply (Real.tendsto_exp_atTop.comp hh').congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact Real.exp_log (mul_pos (by exact_mod_cast (show 0 < m by omega)) (standardNormalUpperTail_pos _))

theorem tendsto_normalMaximumCDF_below_printed_threshold {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun m : ℕ => normalMaximumCDF m (a*printedNormalMaxThreshold m)) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_normalTail_mass_below_printed_max_threshold ha ha1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · exact Eventually.of_forall (fun m => pow_nonneg (standardNormalCDF_nonneg _) m)
  · filter_upwards [] with m
    simpa [neg_mul] using normalMaximumCDF_le_exp_tail_mass m (a*printedNormalMaxThreshold m)

theorem tendsto_normalTail_mass_above_printed_max_threshold {a : ℝ} (ha : 1 < a) :
    Tendsto (fun m : ℕ => (m : ℝ) * standardNormalUpperTail (a * printedNormalMaxThreshold m))
      atTop (𝓝 0) := by
  have hapos : 0 < a := zero_lt_one.trans ha
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_log_normalTail_below_printed_max_threshold hapos)
  have hr' : Tendsto (fun m : ℕ => Real.log ((m : ℝ) *
      standardNormalUpperTail (a * printedNormalMaxThreshold m)) / Real.log (m : ℝ))
      atTop (𝓝 (1 - a ^ 2)) := by
    apply hr.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [Real.log_mul hmp.ne' (standardNormalUpperTail_pos _).ne']
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  have hh := hlog.atTop_mul_neg (by nlinarith : 1 - a ^ 2 < 0) hr'
  have hh' : Tendsto (fun m : ℕ => Real.log ((m : ℝ) *
      standardNormalUpperTail (a * printedNormalMaxThreshold m))) atTop atBot := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  apply (Real.tendsto_exp_atBot.comp hh').congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact Real.exp_log (mul_pos (by exact_mod_cast (show 0 < m by omega)) (standardNormalUpperTail_pos _))

theorem tendsto_normalMaximumCDF_tail_above_printed_threshold {a : ℝ} (ha : 1 < a) :
    Tendsto (fun m : ℕ => 1 - normalMaximumCDF m (a * printedNormalMaxThreshold m)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_normalTail_mass_above_printed_max_threshold ha)
  · exact Eventually.of_forall (fun m => sub_nonneg.mpr
      (pow_le_one₀ (standardNormalCDF_nonneg _) (standardNormalCDF_le_one _) ))
  · exact Eventually.of_forall (fun m => by
      simpa only [normalMaximumCDF, standardNormalUpperTail_eq_one_sub] using
        one_sub_pow_le_nat_mul_one_sub (standardNormalCDF_nonneg (a * printedNormalMaxThreshold m))
          (standardNormalCDF_le_one _) m)
end
end RectangleCLT.Companion.SplitV4.Printed

import RectangleCLTCompanion.WeightedTailComparison
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The literal strict Laplace integration-by-parts identity in F.1,
frozen manuscript lines 3919--3921. Atoms are permitted, including at
zero. The zero parameter is handled separately, and no L1 claim about
the unweighted tail integral is made at that parameter. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Interval

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem strictTailProbability_measurable (μ : Measure ℝ) :
    Measurable (fun t : ℝ => μ.real (Ioi t)) :=
  (show Antitone (fun t : ℝ => μ (Ioi t)) from
    fun _ _ h => measure_mono (Ioi_subset_Ioi h)).measurable.ennreal_toReal

theorem integrable_strict_laplace_weight (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) : Integrable (lowerStrictTailWeight s) μ := by
  apply (integrable_const (1 : ℝ)).mono' (lowerStrictTailWeight_measurable s).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (lowerStrictTailWeight_nonneg _ _)]
    exact lowerStrictTailWeight_le_one hs y

theorem integrable_strict_laplace_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s*t)*μ.real (Ioi t)) (Ioi (0 : ℝ)) := by
  apply (integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0).mono'
    (((measurable_const.mul measurable_id).exp).mul (strictTailProbability_measurable μ)).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) measureReal_nonneg)]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) measureReal_le_one

theorem integrable_strict_laplace_correction (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ => s*(Real.exp (-s*t)*μ.real (Ioi t))) (Ioi (0 : ℝ)) := by
  rcases hs.eq_or_lt with h0 | hp
  · subst s
    simp
  · exact (integrable_strict_laplace_tail μ hp).const_mul s

theorem laplace_decay_primitive (s b : ℝ) :
    (∫ t in (0 : ℝ)..b, s*Real.exp (-s*t)) = 1-Real.exp (-s*b) := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => 1-Real.exp (-s*u)) (s*Real.exp (-s*t)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub (((hasDerivAt_id t).const_mul (-s)).exp) using 1 <;>
      simp only [id_eq] <;> ring
  have hc : Continuous (fun t : ℝ => s*Real.exp (-s*t)) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 b)
  simpa only [mul_zero,Real.exp_zero,sub_self,sub_zero] using he

private def laplaceLoss (s y : ℝ) : ℝ := 1-Real.exp (-s*max y 0)

private theorem laplaceLoss_nonneg {s : ℝ} (hs : 0 ≤ s) (y : ℝ) : 0 ≤ laplaceLoss s y := by
  have hh : Real.exp (-s*max y 0) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [le_max_right y (0 : ℝ)])
  exact sub_nonneg.mpr hh

private theorem integrable_laplaceLoss (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) : Integrable (laplaceLoss s) μ := by
  have hm : Measurable (laplaceLoss s) := by unfold laplaceLoss; fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (laplaceLoss_nonneg hs y)]
    unfold laplaceLoss
    linarith [Real.exp_nonneg (-s*max y 0)]

private theorem integral_laplaceLoss_eq_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) :
    (∫ y, laplaceLoss s y ∂μ) = s*(∫ t in Ioi (0 : ℝ), Real.exp (-s*t)*μ.real (Ioi t)) := by
  have hraw := integrable_strict_laplace_tail μ hs
  have hcorr := integrable_strict_laplace_correction μ hs.le
  have hm : Measurable (laplaceLoss s) := by unfold laplaceLoss; fun_prop
  have hc : Continuous (fun t : ℝ => s*Real.exp (-s*t)) := by fun_prop
  have he := lintegral_comp_eq_lintegral_meas_lt_mul (f := fun y : ℝ => max y 0)
    (g := fun t : ℝ => s*Real.exp (-s*t)) μ
    (ae_of_all _ fun y => le_max_right y 0) (measurable_id.max measurable_const).aemeasurable
    (fun b _ => hc.intervalIntegrable 0 b) (ae_of_all _ fun _ => mul_nonneg hs.le (Real.exp_nonneg _))
  simp_rw [laplace_decay_primitive] at he
  have heq : (∫⁻ t in Ioi (0 : ℝ), μ {y : ℝ | t < max y 0}*ENNReal.ofReal (s*Real.exp (-s*t))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (s*(Real.exp (-s*t)*μ.real (Ioi t))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hset : {y : ℝ | t < max y 0} = Ioi t := by
      ext y
      simp only [mem_setOf_eq,mem_Ioi,lt_max_iff,not_lt_of_ge ht0.le,or_false]
    rw [hset]
    rw [show s*(Real.exp (-s*t)*μ.real (Ioi t)) = (s*Real.exp (-s*t))*μ.real (Ioi t) by ring,
      ENNReal.ofReal_mul (mul_nonneg hs.le (Real.exp_nonneg _))]
    change _ = ENNReal.ofReal (s*Real.exp (-s*t))*ENNReal.ofReal ((μ (Ioi t)).toReal)
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _),mul_comm]
  rw [heq] at he
  have hr := congrArg ENNReal.toReal he
  change (∫⁻ y, ENNReal.ofReal (laplaceLoss s y) ∂μ).toReal = _ at hr
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (laplaceLoss_nonneg hs.le)) hm.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun t => mul_nonneg hs.le (mul_nonneg (Real.exp_nonneg _) measureReal_nonneg))
      hcorr.aestronglyMeasurable,integral_const_mul] at hr
  exact hr

/-- Exact printed strict-tail integration by parts. It permits any atom
at zero. When s=0, the correction vanishes algebraically, as the paper
explicitly specifies; unweighted-tail integrability is asserted only
for positive s in the separate theorem above. -/
theorem strict_laplace_tail_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ y, lowerStrictTailWeight s y ∂μ) = μ.real (Ioi (0 : ℝ))-
      s*(∫ t in Ioi (0 : ℝ), Real.exp (-s*t)*μ.real (Ioi t)) := by
  rcases hs.eq_or_lt with h0 | hp
  · subst s
    have hw : lowerStrictTailWeight 0 = (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
      funext y
      by_cases hy : 0 < y <;> simp [lowerStrictTailWeight,hy]
    rw [hw,integral_indicator_const 1 measurableSet_Ioi]
    simp
  · have he : lowerStrictTailWeight s = (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))-laplaceLoss s := by
      funext y
      by_cases hy : 0 < y
      · simp [lowerStrictTailWeight,laplaceLoss,hy,max_eq_left hy.le]
      · have hmax : max y 0 = 0 := max_eq_right (le_of_not_gt hy)
        simp [lowerStrictTailWeight,laplaceLoss,hy,hmax]
    rw [he]
    change (∫ y, (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) y-laplaceLoss s y ∂μ) = _
    rw [integral_sub (f := (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) (g := laplaceLoss s)
        ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi) (integrable_laplaceLoss μ hp.le),
      integral_indicator_const 1 measurableSet_Ioi,integral_laplaceLoss_eq_tail μ hp]
    simp only [smul_eq_mul,mul_one]

theorem strictTailProbability_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    μ.real (Ioi t) = 1-μ.real (Iic t) := by
  rw [show Ioi t = (Iic t)ᶜ by ext y; simp,measureReal_compl measurableSet_Iic]
  simp

theorem laplace_correction_kernel_mass {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), s*Real.exp (-s*t)) = 1 := by
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : -s < 0) 0]
  simp only [mul_zero,Real.exp_zero]
  field_simp [hs.ne']

/-- The printed CDF comparison now consumes the exact strict Laplace
identity. No continuity/no-atom hypothesis is used, and the atom at zero
is retained by Iic0 in the complement formula. -/
theorem strict_laplace_tail_comparison (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (hCDF : ∀ x, |μ.real (Iic x)-ν.real (Iic x)| ≤ ε) :
    |(∫ y, lowerStrictTailWeight s y ∂μ)-(∫ y, lowerStrictTailWeight s y ∂ν)| ≤ 2*ε := by
  have htail (t : ℝ) : |μ.real (Ioi t)-ν.real (Ioi t)| ≤ ε := by
    rw [strictTailProbability_eq_one_sub_cdf μ,strictTailProbability_eq_one_sub_cdf ν]
    have he : 1-μ.real (Iic t)-(1-ν.real (Iic t)) = ν.real (Iic t)-μ.real (Iic t) := by ring
    rw [he,abs_sub_comm]
    exact hCDF t
  rw [strict_laplace_tail_identity μ hs,strict_laplace_tail_identity ν hs]
  by_cases hs0 : s = 0
  · simp only [hs0,zero_mul,sub_zero]
    exact (htail 0).trans (by linarith)
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    let f : Measure ℝ → ℝ → ℝ := fun κ t => s*(Real.exp (-s*t)*κ.real (Ioi t))
    have hfi : IntegrableOn (f μ) (Ioi (0 : ℝ)) := integrable_strict_laplace_correction μ hs
    have hgi : IntegrableOn (f ν) (Ioi (0 : ℝ)) := integrable_strict_laplace_correction ν hs
    have hki : IntegrableOn (fun t : ℝ => ε*(s*Real.exp (-s*t))) (Ioi (0 : ℝ)) :=
      ((integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0).const_mul s).const_mul ε
    have hbound (t : ℝ) : |f μ t-f ν t| ≤ ε*(s*Real.exp (-s*t)) := by
      have he : f μ t-f ν t = (s*Real.exp (-s*t))*(μ.real (Ioi t)-ν.real (Ioi t)) := by dsimp [f]; ring
      rw [he,abs_mul,abs_of_nonneg (mul_nonneg hs (Real.exp_nonneg _))]
      nlinarith [mul_le_mul_of_nonneg_left (htail t) (mul_nonneg hs (Real.exp_nonneg (-s*t)))]
    have hcorr : |(∫ t in Ioi (0 : ℝ), f μ t)-(∫ t in Ioi (0 : ℝ), f ν t)| ≤ ε := by
      rw [← integral_sub hfi hgi]
      calc
        _ ≤ ∫ t in Ioi (0 : ℝ), |f μ t-f ν t| := abs_integral_le_integral_abs
        _ ≤ ∫ t in Ioi (0 : ℝ), ε*(s*Real.exp (-s*t)) :=
          integral_mono ((hfi.sub hgi).abs) hki hbound
        _ = ε := by rw [integral_const_mul,laplace_correction_kernel_mass hsp,mul_one]
    have he : μ.real (Ioi (0 : ℝ))-s*(∫ t in Ioi (0 : ℝ), Real.exp (-s*t)*μ.real (Ioi t))-
        (ν.real (Ioi (0 : ℝ))-s*(∫ t in Ioi (0 : ℝ), Real.exp (-s*t)*ν.real (Ioi t))) =
        (μ.real (Ioi (0 : ℝ))-ν.real (Ioi (0 : ℝ)))-
          ((∫ t in Ioi (0 : ℝ), f μ t)-(∫ t in Ioi (0 : ℝ), f ν t)) := by
      dsimp only [f]
      rw [integral_const_mul,integral_const_mul]
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith [htail 0,hcorr])

end
end RectangleCLT.Companion.SplitV4.Printed

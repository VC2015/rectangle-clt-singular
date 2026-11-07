import RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusUnion
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Genuine layer-cake integration of the printed adaptive-radius tail.
The numerical cutoff is 8 sqrt L; changing this fixed constant has no
effect on the printed argument. The same tail integral proves genuine L1;
the existing coordinate-MGF radius bound is not used. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem integral_pow_eq_weighted_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω)
    {k : ℕ} (hk : 0 < k) (hi : Integrable (fun ω => R ω^k) μ) :
    (∫ ω, R ω^k ∂μ) = (k : ℝ)*∫ x in Ioi (0 : ℝ),
      x^(k-1)*(μ.real {ω | x < R ω}) := by
  have htail : Measurable (fun x : ℝ => μ.real {ω | x < R ω}) :=
    (show Antitone (fun x : ℝ => μ {ω | x < R ω}) from
      fun _ _ hxy => measure_mono (fun _ h => hxy.trans_lt h)).measurable.ennreal_toReal
  have hnonneg : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ x^(k-1)*μ.real {ω | x < R ω} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _) measureReal_nonneg
  have he := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ hR0) hR.aemeasurable (show (0 : ℝ) < k by exact_mod_cast hk)
  have hexp : (k : ℝ)-1 = ((k-1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  simp only [Real.rpow_natCast, hexp] at he
  have he' := congrArg ENNReal.toReal he
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun ω => pow_nonneg (hR0 ω) k)) hi.aestronglyMeasurable] at he'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg k)] at he'
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg
    ((measurable_id.pow_const _).mul htail).aestronglyMeasurable]
  convert he' using 2
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.ofReal_mul (pow_nonneg hx.le _)]
  change ENNReal.ofReal (x^(k-1))*ENNReal.ofReal ((μ {ω | x < R ω}).toReal) = _
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [mul_comm]

def radialTailMoment (k : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x^(k-1)*Real.exp (-(x^2)/16)

theorem integrable_radialTailMoment (k : ℕ) :
    Integrable (fun x : ℝ => x^(k-1)*Real.exp (-(x^2)/16)) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (b := (1/16 : ℝ)) (by norm_num)
    (s := ((k-1 : ℕ) : ℝ)) (by have hh := Nat.cast_nonneg (α := ℝ) (k-1); linarith)
  convert hi using 1
  funext x
  rw [Real.rpow_natCast]
  congr 2
  ring

theorem radialTailMoment_nonneg (k : ℕ) : 0 ≤ radialTailMoment k := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_nonneg _)

theorem integral_pow_le_of_gaussian_tail_split
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω)
    {k : ℕ} (hk : 0 < k)
    {T : ℝ} (hT : 0 ≤ T)
    (htail : ∀ x, T ≤ x → μ.real {ω | x < R ω} ≤ Real.exp (-(x^2)/16)) :
    Integrable (fun ω => R ω^k) μ ∧
      (∫ ω, R ω^k ∂μ) ≤ T^k+(k : ℝ)*radialTailMoment k := by
  let f : ℝ → ℝ := fun x => x^(k-1)*μ.real {ω | x < R ω}
  let g : ℝ → ℝ := fun x => (Ioc (0 : ℝ) T).indicator (fun x => x^(k-1)) x+
    x^(k-1)*Real.exp (-(x^2)/16)
  have hhead : Integrable ((Ioc (0 : ℝ) T).indicator (fun x : ℝ => x^(k-1))) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    exact ((continuous_id.pow _).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hg : Integrable g := hhead.add (integrable_radialTailMoment k)
  have hfmeas : Measurable f := (measurable_id.pow_const _).mul
    ((show Antitone (fun x : ℝ => μ {ω | x < R ω}) from
      fun _ _ hxy => measure_mono (fun _ h => hxy.trans_lt h)).measurable.ennreal_toReal)
  have hbound : ∀ x ∈ Ioi (0 : ℝ), f x ≤ g x := by
    intro x hx
    have hxpow : 0 ≤ x^(k-1) := pow_nonneg hx.le _
    by_cases hxt : x ≤ T
    · simp only [g, indicator_of_mem (show x ∈ Ioc (0 : ℝ) T from ⟨hx,hxt⟩)]
      have hprob : μ.real {ω | x < R ω} ≤ 1 := measureReal_le_one
      have hh := mul_le_mul_of_nonneg_left hprob hxpow
      dsimp only [f]
      nlinarith [mul_nonneg hxpow (Real.exp_nonneg (-(x^2)/16))]
    · simp only [g, indicator_of_not_mem (show x ∉ Ioc (0 : ℝ) T from fun h => hxt h.2), zero_add]
      exact mul_le_mul_of_nonneg_left (htail x (le_of_not_ge hxt)) hxpow
  have hfi : Integrable f (volume.restrict (Ioi (0 : ℝ))) := by
    apply hg.integrableOn.mono' hfmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.le _) measureReal_nonneg)]
    exact hbound x hx
  have hle := setIntegral_mono_on hfi hg.integrableOn measurableSet_Ioi hbound
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ hR0) hR.aemeasurable (show (0 : ℝ) < k by exact_mod_cast hk)
  have hexp : (k : ℝ)-1 = ((k-1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  simp only [Real.rpow_natCast, hexp] at hlayer
  have htailint : (∫⁻ x in Ioi (0 : ℝ), μ {ω | x < R ω}*ENNReal.ofReal (x^(k-1))) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (f x) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [f]
    rw [ENNReal.ofReal_mul (pow_nonneg hx.le _)]
    change _ = ENNReal.ofReal (x^(k-1))*ENNReal.ofReal ((μ {ω | x < R ω}).toReal)
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]
  have hfinite : (∫⁻ ω, ENNReal.ofReal (R ω^k) ∂μ) < ∞ := by
    rw [hlayer, htailint]
    exact ENNReal.mul_lt_top (by simp) hfi.lintegral_lt_top
  have hi : Integrable (fun ω => R ω^k) μ :=
    ⟨(hR.pow_const k).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => pow_nonneg (hR0 ω) k))).mpr hfinite⟩
  refine ⟨hi, ?_⟩
  have hheadint : (∫ x in Ioi (0 : ℝ), (Ioc (0 : ℝ) T).indicator (fun x : ℝ => x^(k-1)) x) = T^k/(k : ℝ) := by
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc (0 : ℝ) T ⊆ Ioi 0 from fun _ h => h.1),
      ← intervalIntegral.integral_of_le hT, integral_pow]
    have hexp : k-1+1 = k := Nat.sub_add_cancel hk
    simp only [hexp, zero_pow hk.ne', sub_zero]
    have hexpR : ((k-1 : ℕ) : ℝ)+1 = k := by exact_mod_cast hexp
    rw [hexpR]
  dsimp only [g] at hle
  rw [integral_add hhead.integrableOn (integrable_radialTailMoment k).integrableOn,
    hheadint] at hle
  rw [integral_pow_eq_weighted_tail μ R hR hR0 hk hi]
  have hmul := mul_le_mul_of_nonneg_left hle (show (0 : ℝ) ≤ k from Nat.cast_nonneg _)
  dsimp only [f] at hmul
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold radialTailMoment
  convert hmul using 1 <;> field_simp <;> ring

def radiusMomentCoefficient (k : ℕ) : ℝ := 8^k+(k : ℝ)*radialTailMoment k

theorem thresholdProjectionRadius_integrable_from_radial_tail {m r : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector r) {k : ℕ} (hk : 0 < k) :
    Integrable (fun g => thresholdProjectionRadius u g^k) (standardGaussian r) :=
  (integral_pow_le_of_gaussian_tail_split (standardGaussian r)
    (thresholdProjectionRadius u) (measurable_thresholdProjectionRadius u)
    (fun g => zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) hk
    (by positivity : 0 ≤ 8*Real.sqrt (dimensionLog m))
    (fun x hx => thresholdProjectionRadius_tail_beyond_sqrt_log hm u hx)).1

theorem thresholdProjectionRadius_moment_from_radial_tail {m r : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector r) {k : ℕ} (hk : 0 < k) :
    (∫ g, thresholdProjectionRadius u g^k ∂standardGaussian r) ≤
      radiusMomentCoefficient k*(Real.sqrt (dimensionLog m))^k := by
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
  have hs : 1 ≤ Real.sqrt (dimensionLog m) := Real.one_le_sqrt.mpr hL
  have hpow : 1 ≤ (Real.sqrt (dimensionLog m))^k := one_le_pow₀ hs
  have hh := integral_pow_le_of_gaussian_tail_split (standardGaussian r)
    (thresholdProjectionRadius u) (measurable_thresholdProjectionRadius u)
    (fun g => zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) hk
    (by positivity : 0 ≤ 8*Real.sqrt (dimensionLog m))
    (fun x hx => thresholdProjectionRadius_tail_beyond_sqrt_log hm u hx)
  have hh := hh.2
  have htailpos : 0 ≤ (k : ℝ)*radialTailMoment k := mul_nonneg (Nat.cast_nonneg _) (radialTailMoment_nonneg k)
  have htail := mul_le_mul_of_nonneg_left hpow htailpos
  rw [mul_one] at htail
  unfold radiusMomentCoefficient
  rw [mul_pow] at hh
  nlinarith

/-- One fixed numerical constant, chosen before faces, dimensions and
normal vectors, controls both printed radius moments. -/
def projectionRadiusMomentConstant : ℝ := max 1 (max (radiusMomentCoefficient 2) (radiusMomentCoefficient 3))

theorem projectionRadiusMomentConstant_ge_one : 1 ≤ projectionRadiusMomentConstant := le_max_left _ _

theorem thresholdProjectionRadius_second_third_moments_from_radial_tail {m r : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector r) :
    Integrable (fun g => thresholdProjectionRadius u g^2) (standardGaussian r) ∧
    Integrable (fun g => thresholdProjectionRadius u g^3) (standardGaussian r) ∧
    (∫ g, thresholdProjectionRadius u g^2 ∂standardGaussian r) ≤
      projectionRadiusMomentConstant*dimensionLog m ∧
    (∫ g, thresholdProjectionRadius u g^3 ∂standardGaussian r) ≤
      projectionRadiusMomentConstant*(dimensionLog m*Real.sqrt (dimensionLog m)) := by
  have hL : 0 ≤ dimensionLog m := zero_le_one.trans (log_exp_mul_nat_ge_one hm)
  have hs := Real.sq_sqrt hL
  have hc2 : radiusMomentCoefficient 2 ≤ projectionRadiusMomentConstant :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hc3 : radiusMomentCoefficient 3 ≤ projectionRadiusMomentConstant :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨thresholdProjectionRadius_integrable_from_radial_tail hm u (by decide),
    thresholdProjectionRadius_integrable_from_radial_tail hm u (by decide), ?_, ?_⟩
  · have hh := thresholdProjectionRadius_moment_from_radial_tail hm u (k := 2) (by decide)
    rw [hs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hc2 hL)
  · have hh := thresholdProjectionRadius_moment_from_radial_tail hm u (k := 3) (by decide)
    have hp : Real.sqrt (dimensionLog m)^3 = dimensionLog m*Real.sqrt (dimensionLog m) := by
      rw [pow_succ,hs]
    rw [hp] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hc3 (mul_nonneg hL (Real.sqrt_nonneg _)))

end
end RectangleCLT.Companion.SplitV4.Printed

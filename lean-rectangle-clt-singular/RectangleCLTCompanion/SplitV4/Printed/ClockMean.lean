import RectangleCLTCompanion.SplitV4.Printed.ClockTails
import RectangleCLT.Optimization

/-! The printed union bound and layer-cake expectation for the actual
maximum logarithmic threshold displacement. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def clockLogVector (p : ℕ) (e : ℝ × (Face p → ℝ)) : Face p → ℝ :=
  fun f => Real.log (e.2 f/e.1)

def clockLogMaximum (p : ℕ) (e : ℝ × (Face p → ℝ)) : ℝ := ‖clockLogVector p e‖

def randomThresholdRadius (p : ℕ) (h : ℝ) (e : ℝ × (Face p → ℝ)) : ℝ :=
  h*clockLogMaximum p e

def randomThresholdShift (p : ℕ) (h : ℝ) (e : ℝ × (Face p → ℝ)) : Face p → ℝ :=
  h • clockLogVector p e

theorem randomThresholdShift_norm {p : ℕ} {h : ℝ} (hh : 0 ≤ h)
    (e : ℝ × (Face p → ℝ)) :
    ‖randomThresholdShift p h e‖ = randomThresholdRadius p h e := by
  rw [randomThresholdShift,norm_smul,Real.norm_eq_abs,abs_of_nonneg hh]
  rfl

theorem measurable_clockLogMaximum (p : ℕ) : Measurable (clockLogMaximum p) := by
  have hlog (f : Face p) : Measurable (fun e : ℝ × (Face p → ℝ) => Real.log (e.2 f/e.1)) := by
    have hf : Measurable (fun e : ℝ × (Face p → ℝ) => e.2 f) :=
      (measurable_pi_apply f).comp measurable_snd
    exact (hf.div measurable_fst).log
  exact (measurable_pi_lambda _ hlog).norm

theorem clockLogMaximum_nonneg (p : ℕ) (e : ℝ × (Face p → ℝ)) :
    0 ≤ clockLogMaximum p e := norm_nonneg _

theorem randomThresholdRadius_shift_le {p : ℕ} {h : ℝ} (hh : 0 ≤ h)
    (e : ℝ × (Face p → ℝ)) (f : Face p) :
    |h*Real.log (e.2 f/e.1)| ≤ randomThresholdRadius p h e := by
  rw [abs_mul,abs_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (clockLogVector p e) f) hh

theorem clockLogMaximum_tail_le {p : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    (exponentialRectangleLaw p).real {e | s < clockLogMaximum p e} ≤
      4*(p : ℝ)*Real.exp (-s) := by
  classical
  have hset : {e : ℝ × (Face p → ℝ) | s < clockLogMaximum p e} =
      ⋃ f : Face p, {e | s < |Real.log (e.2 f/e.1)|} := by
    ext e
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · intro he
      by_contra hn
      push_neg at hn
      have hh : ‖clockLogVector p e‖ ≤ s := (pi_norm_le_iff_of_nonneg hs).mpr hn
      exact (not_lt_of_ge hh) he
    · rintro ⟨f,hf⟩
      exact hf.trans_le (norm_le_pi_norm (clockLogVector p e) f)
  rw [hset]
  calc
    _ ≤ ∑ f : Face p, (exponentialRectangleLaw p).real
        {e | s < |Real.log (e.2 f/e.1)|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _f : Face p, 2*Real.exp (-s) :=
      Finset.sum_le_sum (fun f _ => clock_abs_log_ratio_tail_le f hs)
    _ = _ := by simp [Face]; ring

theorem clockLogMaximum_tail_le_min {p : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    (exponentialRectangleLaw p).real {e | s < clockLogMaximum p e} ≤
      min 1 (4*(p : ℝ)*Real.exp (-s)) :=
  le_min measureReal_le_one (clockLogMaximum_tail_le hs)

theorem randomThresholdRadius_tail_le_min {p : ℕ} {h s : ℝ} (hh : 0 < h) (hs : 0 ≤ s) :
    (exponentialRectangleLaw p).real {e | h*s < randomThresholdRadius p h e} ≤
      min 1 (4*(p : ℝ)*Real.exp (-s)) := by
  have hset : {e | h*s < randomThresholdRadius p h e} =
      {e | s < clockLogMaximum p e} := by
    ext e
    exact mul_lt_mul_left hh
  rw [hset]
  exact clockLogMaximum_tail_le_min hs

/-- Literal layer-cake integration of a probability tail bounded by
`min(1,N*exp(-s))`. Integrability is a conclusion, never an assumption. -/
theorem integral_le_log_add_one_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {N : ℝ} (hN : 1 ≤ N)
    (htail : ∀ s, 0 ≤ s → μ.real {ω | s < X ω} ≤ N*Real.exp (-s)) :
    Integrable X μ ∧ (∫ ω, X ω ∂μ) ≤ Real.log N+1 := by
  let a := Real.log N
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have ha : 0 ≤ a := Real.log_nonneg hN
  let B : ℝ → ℝ := fun t => (Ioc 0 a).indicator (fun _ => 1) t+
    N*(Ioi a).indicator (fun t => Real.exp (-t)) t
  have hB0 (t) : 0 ≤ B t := add_nonneg
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (mul_nonneg hNp.le (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _))
  have hI : Integrable ((Ioc 0 a).indicator (fun _ => (1 : ℝ))) volume :=
    (integrableOn_const.mpr (Or.inr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top))).integrable_indicator measurableSet_Ioc
  have hJ : Integrable ((Ioi a).indicator (fun t => Real.exp (-t))) volume :=
    (integrableOn_exp_neg_Ioi a).integrable_indicator measurableSet_Ioi
  have hBi : Integrable B volume := hI.add (hJ.const_mul N)
  have hBint : (∫ t, B t) = a+1 := by
    rw [integral_add hI (hJ.const_mul N),integral_const_mul,
      integral_indicator_const (1 : ℝ) measurableSet_Ioc,
      integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi,
      Real.volume_real_Ioc_of_le ha]
    simp only [sub_zero, smul_eq_mul, mul_one]
    dsimp [a]
    rw [Real.exp_neg,Real.exp_log hNp]
    field_simp
  have hpoint (s : ℝ) (hs : 0 < s) : μ {ω | s < X ω} ≤ ENNReal.ofReal (B s) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    by_cases hsa : s ≤ a
    · have hi : s ∈ Ioc 0 a := ⟨hs,hsa⟩
      have hj : s ∉ Ioi a := not_lt_of_ge hsa
      simpa only [B,Set.indicator_of_mem hi,Set.indicator_of_not_mem hj,mul_zero,add_zero]
        using (measureReal_le_one (μ := μ) (s := {ω | s < X ω}))
    · have hi : s ∉ Ioc 0 a := fun h => hsa h.2
      have hj : s ∈ Ioi a := lt_of_not_ge hsa
      simpa only [B,Set.indicator_of_not_mem hi,Set.indicator_of_mem hj,zero_add]
        using htail s hs.le
  have hlin : (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) ≤ ENNReal.ofReal (a+1) := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hX0) hXm.aemeasurable]
    calc
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (B s) :=
        setLIntegral_mono' measurableSet_Ioi (fun s hs => hpoint s hs)
      _ ≤ ∫⁻ s, ENNReal.ofReal (B s) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (a+1) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hBi (ae_of_all _ hB0),hBint]
  have hXi : Integrable X μ := ⟨hXm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hX0)).mpr
      (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hXi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ a+1 by linarith)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hXi (ae_of_all _ hX0)]
  exact hlin

theorem integrable_clockLogMaximum {p : ℕ} (hp : 1 ≤ p) :
    Integrable (clockLogMaximum p) (exponentialRectangleLaw p) :=
  (integral_le_log_add_one_of_exponential_tail (exponentialRectangleLaw p)
    (clockLogMaximum p) (measurable_clockLogMaximum p) (clockLogMaximum_nonneg p)
    (N := 4*(p : ℝ)) (by exact_mod_cast (show 1 ≤ 4*p by omega))
    (fun s hs => clockLogMaximum_tail_le hs)).1

theorem integral_clockLogMaximum_le {p : ℕ} (hp : 1 ≤ p) :
    (∫ e, clockLogMaximum p e ∂exponentialRectangleLaw p) ≤ Real.log (4*(p : ℝ))+1 :=
  (integral_le_log_add_one_of_exponential_tail (exponentialRectangleLaw p)
    (clockLogMaximum p) (measurable_clockLogMaximum p) (clockLogMaximum_nonneg p)
    (N := 4*(p : ℝ)) (by exact_mod_cast (show 1 ≤ 4*p by omega))
    (fun s hs => clockLogMaximum_tail_le hs)).2

theorem integrable_randomThresholdRadius {p : ℕ} (hp : 1 ≤ p) (h : ℝ) :
    Integrable (randomThresholdRadius p h) (exponentialRectangleLaw p) :=
  (integrable_clockLogMaximum hp).const_mul h

theorem integral_randomThresholdRadius_le {p : ℕ} (hp : 1 ≤ p) {h : ℝ} (hh : 0 ≤ h) :
    (∫ e, randomThresholdRadius p h e ∂exponentialRectangleLaw p) ≤
      h*(Real.log (4*(p : ℝ))+1) := by
  change (∫ e, h*clockLogMaximum p e ∂exponentialRectangleLaw p) ≤ _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_clockLogMaximum_le hp) hh

theorem integral_randomThresholdRadius_le_log {p : ℕ} (hp : 1 ≤ p) {h : ℝ} (hh : 0 ≤ h) :
    (∫ e, randomThresholdRadius p h e ∂exponentialRectangleLaw p) ≤ 4*h*dimensionLog p := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at ht ⊢
    exact ht
  have heq : Real.log (4*(p : ℝ))+1 = dimensionLog p+Real.log 4 := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hpR.ne']
    unfold dimensionLog
    rw [Real.log_mul (Real.exp_ne_zero _) hpR.ne',Real.log_exp]
    ring
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hb := integral_randomThresholdRadius_le hp hh
  rw [heq] at hb
  have hscale := mul_le_mul_of_nonneg_left hL hh
  nlinarith [mul_le_mul_of_nonneg_left hlog4 hh]

end
end RectangleCLT.Companion.SplitV4.Printed

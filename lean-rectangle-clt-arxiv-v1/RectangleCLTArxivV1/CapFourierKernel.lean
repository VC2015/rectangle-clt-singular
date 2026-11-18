import RectangleCLTArxivV1.ExpectedMaximum
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Compact-frequency kernels for small-box concentration. The first
identity expands an actual squared Fourier kernel and applies Fubini;
it assumes no small-ball probability estimate or density of the law. -/

namespace RectangleCLTArxivV1

open MeasureTheory ComplexConjugate

noncomputable section

/-- The average character on a chosen frequency probability law. -/
def frequencyKernel {T Ω : Type*} [MeasurableSpace T]
    (ν : Measure T) (χ : T × Ω → ℂ) (ω : Ω) : ℂ :=
  ∫ t, χ (t,ω) ∂ν

/-- Squaring a genuine compact-frequency kernel exposes the characteristic
function of two independent frequencies. This is the Fubini step underlying
the sinc-squared smoothing argument. -/
theorem integral_frequencyKernel_sq_le_correlation
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (ν : Measure T) [IsProbabilityMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (χ : T × Ω → ℂ) (hχ : Measurable χ) (hb : ∀ z, ‖χ z‖ ≤ 1) :
    (∫ ω, ‖frequencyKernel ν χ ω‖ ^ 2 ∂μ) ≤
      ∫ z : T × T, ‖∫ ω, χ (z.1,ω) * conj (χ (z.2,ω)) ∂μ‖ ∂ν.prod ν := by
  let H : (T × T) × Ω → ℂ := fun z => χ (z.1.1,z.2) * conj (χ (z.1.2,z.2))
  have hHm : Measurable H :=
    (hχ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hχ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hHb (z : (T × T) × Ω) : ‖H z‖ ≤ 1 := by
    dsimp only [H]
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (hb _) (hb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hHi : Integrable H ((ν.prod ν).prod μ) :=
    (integrable_const (1 : ℝ)).mono' hHm.aestronglyMeasurable (ae_of_all _ hHb)
  have hpoint (ω : Ω) : ‖frequencyKernel ν χ ω‖ ^ 2 =
      (∫ z : T × T, H (z,ω) ∂ν.prod ν).re := by
    have heq := integral_prod_mul (μ := ν) (ν := ν)
      (fun t => χ (t,ω)) (fun t => conj (χ (t,ω)))
    rw [integral_conj] at heq
    change (∫ z : T × T, H (z,ω) ∂ν.prod ν) =
      frequencyKernel ν χ ω * conj (frequencyKernel ν χ ω) at heq
    rw [heq, Complex.mul_conj]
    exact (Complex.normSq_eq_norm_sq _).symm
  calc
    _ = ∫ ω, (∫ z : T × T, H (z,ω) ∂ν.prod ν).re ∂μ :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = (∫ ω, ∫ z : T × T, H (z,ω) ∂ν.prod ν ∂μ).re :=
      integral_re hHi.swap.integral_prod_left
    _ = (∫ z : T × T, ∫ ω, H (z,ω) ∂μ ∂ν.prod ν).re := by
      exact congrArg Complex.re (integral_integral_swap hHi.swap)
    _ = ∫ z : T × T, (∫ ω, H (z,ω) ∂μ).re ∂ν.prod ν :=
      (integral_re hHi.integral_prod_left).symm
    _ ≤ _ := by
      apply integral_mono hHi.integral_prod_left.re hHi.integral_prod_left.norm
      intro z
      exact Complex.re_le_norm _

/-- A kernel whose real part is bounded below on an event controls its
actual probability. This step uses positivity, not a density of the law. -/
theorem probability_le_frequencyKernel_sq
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (ν : Measure T) [IsProbabilityMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (χ : T × Ω → ℂ) (hχ : Measurable χ) (hb : ∀ z, ‖χ z‖ ≤ 1)
    (S : Set Ω) (hS : MeasurableSet S)
    (hpos : ∀ ω ∈ S, (1/2 : ℝ) ≤ (frequencyKernel ν χ ω).re) :
    μ.real S ≤ 4*(∫ ω, ‖frequencyKernel ν χ ω‖ ^ 2 ∂μ) := by
  have hKm : Measurable (frequencyKernel ν χ) :=
    hχ.stronglyMeasurable.integral_prod_left'.measurable
  have hKb (ω : Ω) : ‖frequencyKernel ν χ ω‖ ≤ 1 := by
    have hh := norm_integral_le_of_norm_le_const (μ := ν)
      (ae_of_all _ (fun t => hb (t,ω)))
    simpa only [frequencyKernel,measureReal_univ_eq_one,mul_one] using hh
  have hKi : Integrable (fun ω => ‖frequencyKernel ν χ ω‖ ^ 2) μ := by
    apply (integrable_const (1:ℝ)).mono' (hKm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [hKb ω,norm_nonneg (frequencyKernel ν χ ω)]
  have hpoint (ω : Ω) : S.indicator (fun _ => (1:ℝ)) ω ≤
      4*‖frequencyKernel ν χ ω‖ ^ 2 := by
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have hh := (hpos ω hω).trans (Complex.re_le_norm _)
      nlinarith [norm_nonneg (frequencyKernel ν χ ω)]
    · rw [Set.indicator_of_not_mem hω]
      positivity
  rw [← integral_indicator_one hS]
  exact (integral_mono ((integrable_const (1:ℝ)).indicator hS)
    (hKi.const_mul 4) hpoint).trans_eq (integral_const_mul _ _)

/-- The compact-frequency comparison before any characteristic-function
estimate is inserted. -/
theorem probability_le_frequency_correlation
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (ν : Measure T) [IsProbabilityMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (χ : T × Ω → ℂ) (hχ : Measurable χ) (hb : ∀ z, ‖χ z‖ ≤ 1)
    (S : Set Ω) (hS : MeasurableSet S)
    (hpos : ∀ ω ∈ S, (1/2 : ℝ) ≤ (frequencyKernel ν χ ω).re) :
    μ.real S ≤ 4*(∫ z : T × T, ‖∫ ω, χ (z.1,ω)*conj (χ (z.2,ω)) ∂μ‖ ∂ν.prod ν) :=
  (probability_le_frequencyKernel_sq ν μ χ hχ hb S hS hpos).trans
    (mul_le_mul_of_nonneg_left (integral_frequencyKernel_sq_le_correlation ν μ χ hχ hb) (by norm_num))

/-- A phase of magnitude at most one makes the averaged character's real
part at least one half. This is the kernel lower bound on a small box. -/
theorem realPhaseAverage_re_ge_half {T : Type*} [MeasurableSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν] (f : T → ℝ) (hf : Measurable f)
    (hsmall : ∀ᵐ t ∂ν, |f t| ≤ 1) :
    (1/2 : ℝ) ≤ (∫ t, Complex.exp ((f t : ℂ)*Complex.I) ∂ν).re := by
  have hm : Measurable (fun t => Complex.exp ((f t : ℂ)*Complex.I)) :=
    ((Complex.continuous_ofReal.measurable.comp hf).mul_const Complex.I).cexp
  have hb (t : T) : ‖Complex.exp ((f t : ℂ)*Complex.I)‖ ≤ 1 := by
    simp [Complex.norm_exp]
  have hi : Integrable (fun t => Complex.exp ((f t : ℂ)*Complex.I)) ν :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ hb)
  have hlow := integral_mono_ae (integrable_const (1/2:ℝ)) hi.re
    (hsmall.mono (fun t ht => by
      change (1/2:ℝ) ≤ (Complex.exp ((f t:ℂ)*Complex.I)).re
      rw [Complex.exp_ofReal_mul_I_re]
      have hs : (f t)^2 ≤ 1 := by
        have ha := abs_le.mp ht
        nlinarith [sq_nonneg (f t)]
      linarith [Real.one_sub_sq_div_two_le_cos (x := f t)]))
  rw [integral_re hi] at hlow
  simpa only [integral_const,measureReal_univ_eq_one,one_smul] using hlow

/-- A uniform frequency average of a translated nonnegative integrable
function is at most its full integral divided by the frequency volume. -/
theorem integral_cond_sub_le {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd G] [MeasurableNeg G] [MeasurableSub₂ G] (mFreq : Measure G)
    [mFreq.IsNegInvariant] [mFreq.IsAddLeftInvariant] (B : Set G) (Q : G → ℝ)
    (hQ : Integrable Q mFreq) (hQ0 : ∀ t, 0 ≤ Q t) (s : G) :
    (∫ t, Q (s-t) ∂ProbabilityTheory.cond mFreq B) ≤
      (mFreq B).toReal⁻¹ * ∫ t, Q t ∂mFreq := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have hi : Integrable (fun t => Q (s-t)) mFreq :=
    ((Measure.measurePreserving_sub_left mFreq s).integrable_comp hQ.aestronglyMeasurable).mpr hQ
  exact (setIntegral_le_integral hi (ae_of_all _ (fun t => hQ0 (s-t)))).trans_eq
    (integral_sub_left_eq_self Q mFreq s)

/-- Uniform compact-frequency averaging converts a characteristic-function
majorant into an actual probability bound. The majorant is required only
on differences of frequencies inside the chosen compact set. -/
theorem probability_le_uniform_frequency_integral
    {G Ω : Type*} [MeasurableSpace G] [MeasurableSpace Ω] [AddCommGroup G]
    [MeasurableAdd G] [MeasurableNeg G] [MeasurableSub₂ G] (mFreq : Measure G)
    [mFreq.IsNegInvariant] [mFreq.IsAddLeftInvariant] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Set G) (hB : MeasurableSet B)
    (hB0 : mFreq B ≠ 0) (hBfinite : mFreq B ≠ ⊤)
    (χ : G × Ω → ℂ) (hχ : Measurable χ) (hb : ∀ z, ‖χ z‖ ≤ 1)
    (Q : G → ℝ) (hQ : Integrable Q mFreq) (hQm : Measurable Q)
    (hQ0 : ∀ t, 0 ≤ Q t) (hQ1 : ∀ t, Q t ≤ 1)
    (S : Set Ω) (hS : MeasurableSet S)
    (hpos : ∀ ω ∈ S, (1/2 : ℝ) ≤
      (frequencyKernel (ProbabilityTheory.cond mFreq B) χ ω).re)
    (hdecay : ∀ s ∈ B, ∀ t ∈ B,
      ‖∫ ω, χ (s,ω)*conj (χ (t,ω)) ∂μ‖ ≤ Q (s-t)) :
    μ.real S ≤ 4*(mFreq B).toReal⁻¹*(∫ t, Q t ∂mFreq) := by
  let ν := ProbabilityTheory.cond mFreq B
  letI : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hB0 hBfinite
  let H : (G × G) × Ω → ℂ :=
    fun z => χ (z.1.1,z.2)*conj (χ (z.1.2,z.2))
  have hHm : Measurable H :=
    (hχ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hχ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hHb (z : (G × G) × Ω) : ‖H z‖ ≤ 1 := by
    dsimp only [H]
    rw [norm_mul,Complex.norm_conj]
    exact (mul_le_mul (hb _) (hb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hCm : Measurable (fun z : G × G =>
      ∫ ω, H (z,ω) ∂μ) := hHm.stronglyMeasurable.integral_prod_right'.measurable
  have hCb (z : G × G) : ‖∫ ω, H (z,ω) ∂μ‖ ≤ 1 := by
    have hh := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (fun ω => hHb (z,ω)))
    simpa only [measureReal_univ_eq_one,mul_one] using hh
  have hCi : Integrable (fun z : G × G =>
      ‖∫ ω, H (z,ω) ∂μ‖) (ν.prod ν) := by
    apply (integrable_const (1:ℝ)).mono' hCm.norm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by rw [norm_norm]; exact hCb z)
  have hQdiff : Integrable (fun z : G × G => Q (z.1-z.2)) (ν.prod ν) := by
    apply (integrable_const (1:ℝ)).mono'
      (hQm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      change ‖Q (z.1-z.2)‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (hQ0 _)]; exact hQ1 _)
  have hmem : ∀ᵐ s ∂ν, s ∈ B := ProbabilityTheory.ae_cond_mem hB
  have hcmp : (∫ z : G × G, ‖∫ ω, H (z,ω) ∂μ‖ ∂ν.prod ν) ≤
      ∫ z : G × G, Q (z.1-z.2) ∂ν.prod ν := by
    apply integral_mono_ae hCi hQdiff
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmem,
      Measure.quasiMeasurePreserving_snd.ae hmem] with z hs ht
    exact hdecay z.1 hs z.2 ht
  have hbound : (∫ z : G × G, Q (z.1-z.2) ∂ν.prod ν) ≤
      (mFreq B).toReal⁻¹*(∫ t, Q t ∂mFreq) := by
    rw [integral_prod _ hQdiff]
    have hh := integral_mono hQdiff.integral_prod_left (integrable_const
      ((mFreq B).toReal⁻¹*(∫ t, Q t ∂mFreq))) (fun s => integral_cond_sub_le mFreq B Q hQ hQ0 s)
    simpa only [integral_const,measureReal_univ_eq_one,one_smul] using hh
  have hp := probability_le_frequency_correlation ν μ χ hχ hb S hS hpos
  exact (hp.trans (mul_le_mul_of_nonneg_left (hcmp.trans hbound) (by norm_num))).trans_eq (by ring)

end
end RectangleCLTArxivV1

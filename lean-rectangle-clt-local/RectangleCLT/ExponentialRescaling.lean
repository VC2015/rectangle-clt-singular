import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual exponential-law changes of variables used to control separate
local suprema in the fourth-order Gaussian face estimate. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT

/-- Multiplication changes the exponential rate by the reciprocal scale. -/
theorem exponential_map_mul {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (expMeasure r).map (fun x => a * x) = expMeasure (r / a) := by
  letI := isProbabilityMeasureExponential hr
  letI := isProbabilityMeasureExponential (div_pos hr ha)
  letI : IsProbabilityMeasure ((expMeasure r).map (fun x => a * x)) :=
    isProbabilityMeasure_map (measurable_const_mul a).aemeasurable
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (measurable_const_mul a) measurableSet_Iic]
  have hpre : (fun y : ℝ => a * y) ⁻¹' Set.Iic x = Set.Iic (x / a) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ ha, mul_comm a y]
  rw [hpre, ← ofReal_cdf (expMeasure r) (x / a), ← ofReal_cdf (expMeasure (r / a)) x]
  change ENNReal.ofReal (exponentialCDFReal r (x / a)) =
    ENNReal.ofReal (exponentialCDFReal (r / a) x)
  rw [exponentialCDFReal_eq hr, exponentialCDFReal_eq (div_pos hr ha)]
  have hsign : 0 ≤ x / a ↔ 0 ≤ x := by
    rw [le_div_iff₀ ha]
    simp
  simp only [hsign]
  split_ifs
  · congr 3
    ring
  · rfl

/-- A larger exponential rate is dominated by that rate times the unit law. -/
theorem exponential_le_rate_mul_unit {r : ℝ} (hr : 1 ≤ r) :
    expMeasure r ≤ ENNReal.ofReal r • expMeasure 1 := by
  change volume.withDensity (exponentialPDF r) ≤
    ENNReal.ofReal r • volume.withDensity (exponentialPDF 1)
  have hm : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [← withDensity_smul (f := exponentialPDF 1) (ENNReal.ofReal r) hm]
  apply withDensity_mono
  exact ae_of_all _ (fun x => by
    by_cases hx : 0 ≤ x
    · simp only [exponentialPDF_of_nonneg hx, Pi.smul_apply, smul_eq_mul, one_mul]
      rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ r)]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ r)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hr hx]
    · simp [exponentialPDF_of_neg (lt_of_not_ge hx)])

/-- Shrinking a unit exponential has density ratio at most the reciprocal
scale. This is a bound on the actual probability measures. -/
theorem unitExponential_map_mul_le {a : ℝ} (ha : 0 < a) (haone : a ≤ 1) :
    (expMeasure 1).map (fun x => a * x) ≤ ENNReal.ofReal a⁻¹ • expMeasure 1 := by
  rw [exponential_map_mul (by norm_num) ha, one_div]
  exact exponential_le_rate_mul_unit ((one_le_inv₀ ha).mpr haone)

/-- Monotonicity of the genuine finite product measure in its factors. -/
theorem finiteProduct_measure_mono {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ ν : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (hle : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have houter : (Measure.pi μ).toOuterMeasure ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    change Measure.pi μ (Set.pi Set.univ s) ≤ _
    rw [Measure.pi_pi]
    exact Finset.prod_le_prod' (fun i _ => hle i (s i))
  apply Measure.le_iff.mpr
  intro s hs
  have htarget : Measure.pi ν s =
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) s := by
    rw [Measure.pi, toMeasure_apply _ _ hs]
  rw [htarget]
  exact houter s

theorem finiteProduct_measure_smul {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i < ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI : ∀ i, IsFiniteMeasure (c i • μ i) := fun i =>
    ⟨by simpa only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using hc i⟩
  apply Measure.pi_eq
  intro s _hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

/-- Independent scaling preserves independence and changes each exponential
rate by the reciprocal scale. -/
theorem unitExponential_pi_map_mul {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (Measure.pi (fun _ : ι => expMeasure 1)).map (fun x i => a i * x i) =
      Measure.pi (fun i => expMeasure (a i)⁻¹) := by
  haveI : ∀ i, IsProbabilityMeasure (expMeasure (a i)⁻¹) :=
    fun i => isProbabilityMeasureExponential (inv_pos.mpr (ha i))
  exact (measurePreserving_pi (fun _ : ι => expMeasure 1)
    (fun i => expMeasure (a i)⁻¹) (fun i =>
      ⟨measurable_const_mul (a i), by
        simpa only [one_div] using
          (exponential_map_mul (r := 1) (by norm_num) (ha i))⟩)).map_eq

/-- Dimension-free product-density domination; coordinates with scale one
contribute the factor one, regardless of the number of inactive faces. -/
theorem unitExponential_pi_map_mul_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (haone : ∀ i, a i ≤ 1) :
    (Measure.pi (fun _ : ι => expMeasure 1)).map (fun x i => a i * x i) ≤
      (∏ i, ENNReal.ofReal (a i)⁻¹) • Measure.pi (fun _ : ι => expMeasure 1) := by
  letI := isProbabilityMeasureExponential (by norm_num : (0 : ℝ) < 1)
  haveI : ∀ i, IsProbabilityMeasure (expMeasure (a i)⁻¹) :=
    fun i => isProbabilityMeasureExponential (inv_pos.mpr (ha i))
  rw [unitExponential_pi_map_mul a ha]
  exact (finiteProduct_measure_mono _ _ (fun i =>
    exponential_le_rate_mul_unit ((one_le_inv₀ (ha i)).mpr (haone i)))).trans_eq
      (finiteProduct_measure_smul (fun _ : ι => expMeasure 1)
        (fun i => ENNReal.ofReal (a i)⁻¹) (fun _ => ENNReal.ofReal_lt_top))

/-- Integral form of the product-density bound, for arbitrary nonnegative
measurable tests, including unbounded tests. -/
theorem unitExponential_pi_lintegral_scale_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (haone : ∀ i, a i ≤ 1)
    (H : (ι → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x, H (fun i => a i * x i) ∂Measure.pi (fun _ : ι => expMeasure 1)) ≤
      (∏ i, ENNReal.ofReal (a i)⁻¹) *
        ∫⁻ x, H x ∂Measure.pi (fun _ : ι => expMeasure 1) := by
  rw [← lintegral_map hH (measurable_pi_lambda _ (fun i =>
    measurable_const.mul (measurable_pi_apply i)))]
  calc
    _ ≤ ∫⁻ x, H x ∂((∏ i, ENNReal.ofReal (a i)⁻¹) •
        Measure.pi (fun _ : ι => expMeasure 1)) :=
      lintegral_mono' (unitExponential_pi_map_mul_le a ha haone) le_rfl
    _ = _ := by rw [lintegral_smul_measure]; rfl

theorem exponentialPDFReal_formula (r x : ℝ) :
    exponentialPDFReal r x = if 0 ≤ x then r * Real.exp (-(r * x)) else 0 := by
  unfold exponentialPDFReal gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]

theorem integral_exponentialPDFReal {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, exponentialPDFReal r x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (exponentialPDFReal_nonneg hr))
    (measurable_exponentialPDFReal r).aestronglyMeasurable]
  change (∫⁻ x : ℝ, exponentialPDF r x).toReal = 1
  rw [lintegral_exponentialPDF_eq_one hr, ENNReal.toReal_one]

/-- The actual Laplace transform needed for the random-rectangle mixture. -/
theorem unitExponential_laplace {q : ℝ} (hq : 0 ≤ q) :
    (∫ x : ℝ, Real.exp (-q * x) ∂expMeasure 1) = 1 / (1 + q) := by
  have hr : 0 < 1 + q := by linarith
  have hm : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  change (∫ x : ℝ, Real.exp (-q * x) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hreal (x : ℝ) : (exponentialPDF 1 x).toReal = exponentialPDFReal 1 x :=
    ENNReal.toReal_ofReal (exponentialPDFReal_nonneg (by norm_num) x)
  simp only [hreal, smul_eq_mul]
  have hpoint (x : ℝ) : exponentialPDFReal 1 x * Real.exp (-q * x) =
      (1 + q)⁻¹ * exponentialPDFReal (1 + q) x := by
    rw [exponentialPDFReal_formula, exponentialPDFReal_formula]
    split_ifs
    · simp only [one_mul]
      rw [← Real.exp_add]
      have heq : -x + -q * x = -((1 + q) * x) := by ring
      rw [heq]
      field_simp
    · simp
  simp_rw [hpoint]
  rw [integral_const_mul, integral_exponentialPDFReal hr, mul_one, one_div]

end RectangleCLT

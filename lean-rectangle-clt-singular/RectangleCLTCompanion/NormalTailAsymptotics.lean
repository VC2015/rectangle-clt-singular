import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Standard normal tails

All distribution functions below refer to the actual standard Gaussian law.
The Mills inequalities are obtained from its density by integration by parts.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable def standardNormalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x
noncomputable def standardNormalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Iic x)
noncomputable def standardNormalUpperTail (x : ℝ) : ℝ := (gaussianReal 0 1).real (Ioi x)

lemma standardNormalPDF_eq (x : ℝ) :
    standardNormalPDF x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x^2 / 2) := by
  simp [standardNormalPDF, gaussianPDFReal]

lemma standardNormalPDF_pos (x : ℝ) : 0 < standardNormalPDF x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

lemma standardNormalPDF_nonneg (x : ℝ) : 0 ≤ standardNormalPDF x :=
  (standardNormalPDF_pos x).le

lemma integrable_standardNormalPDF : Integrable standardNormalPDF :=
  integrable_gaussianPDFReal 0 1

lemma hasDerivAt_standardNormalPDF (x : ℝ) :
    HasDerivAt standardNormalPDF (-x * standardNormalPDF x) x := by
  have hd := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hd using 1
  · ext y
    exact standardNormalPDF_eq y
  · simp only [id_eq, standardNormalPDF_eq]
    ring

lemma continuous_standardNormalPDF : Continuous standardNormalPDF :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_standardNormalPDF x).continuousAt

lemma standardNormalCDF_eq_integral (x : ℝ) :
    standardNormalCDF x = ∫ y in Iic x, standardNormalPDF y := by
  rw [standardNormalCDF, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero]
  exact ENNReal.toReal_ofReal (integral_nonneg fun y => standardNormalPDF_nonneg y)

lemma standardNormalUpperTail_eq_integral (x : ℝ) :
    standardNormalUpperTail x = ∫ y in Ioi x, standardNormalPDF y := by
  rw [standardNormalUpperTail, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero]
  exact ENNReal.toReal_ofReal (integral_nonneg fun y => standardNormalPDF_nonneg y)

lemma standardNormalUpperTail_eq_one_sub (x : ℝ) :
    standardNormalUpperTail x = 1 - standardNormalCDF x := by
  rw [standardNormalUpperTail, ← compl_Iic, measureReal_compl measurableSet_Iic]
  simp [standardNormalCDF]

lemma standardNormalCDF_eq_cdf : standardNormalCDF = cdf (gaussianReal 0 1) := by
  funext x
  exact (cdf_eq_real _ x).symm

lemma standardNormalCDF_nonneg (x : ℝ) : 0 ≤ standardNormalCDF x := by
  rw [standardNormalCDF_eq_cdf]
  exact cdf_nonneg _ x

lemma standardNormalCDF_le_one (x : ℝ) : standardNormalCDF x ≤ 1 := by
  rw [standardNormalCDF_eq_cdf]
  exact cdf_le_one _ x

lemma hasDerivAt_standardNormalCDF (x : ℝ) :
    HasDerivAt standardNormalCDF (standardNormalPDF x) x := by
  have heq : standardNormalCDF = fun u => standardNormalCDF 0 +
      ∫ y in (0 : ℝ)..u, standardNormalPDF y := by
    funext u
    rw [standardNormalCDF_eq_integral u, standardNormalCDF_eq_integral 0,
      ← intervalIntegral.integral_Iic_sub_Iic
        integrable_standardNormalPDF.integrableOn integrable_standardNormalPDF.integrableOn]
    ring
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (integrable_standardNormalPDF.intervalIntegrable)
    continuous_standardNormalPDF.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_standardNormalPDF.continuousAt).const_add _

lemma continuous_standardNormalCDF : Continuous standardNormalCDF :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_standardNormalCDF x).continuousAt

lemma strictMono_standardNormalCDF : StrictMono standardNormalCDF :=
  strictMono_of_hasDerivAt_pos hasDerivAt_standardNormalCDF standardNormalPDF_pos

lemma standardNormalCDF_pos (x : ℝ) : 0 < standardNormalCDF x :=
  lt_of_le_of_lt (standardNormalCDF_nonneg (x-1))
    (strictMono_standardNormalCDF (by linarith : x-1 < x))

lemma standardNormalCDF_lt_one (x : ℝ) : standardNormalCDF x < 1 :=
  lt_of_lt_of_le (strictMono_standardNormalCDF (by linarith : x < x+1))
    (standardNormalCDF_le_one (x+1))

lemma standardNormalUpperTail_pos (x : ℝ) : 0 < standardNormalUpperTail x := by
  rw [standardNormalUpperTail_eq_one_sub]
  exact sub_pos.mpr (standardNormalCDF_lt_one x)

lemma tendsto_standardNormalCDF_atTop : Tendsto standardNormalCDF atTop (𝓝 1) := by
  rw [standardNormalCDF_eq_cdf]
  exact tendsto_cdf_atTop _

lemma tendsto_standardNormalCDF_atBot : Tendsto standardNormalCDF atBot (𝓝 0) := by
  rw [standardNormalCDF_eq_cdf]
  exact tendsto_cdf_atBot _

lemma tendsto_standardNormalPDF_atTop : Tendsto standardNormalPDF atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x^2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  rw [show standardNormalPDF = (fun x : ℝ =>
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x^2/2)) from funext standardNormalPDF_eq]
  simpa only [Function.comp_def, neg_div, mul_zero] using
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul
      ((Real.sqrt (2 * Real.pi))⁻¹)

lemma integrable_mul_standardNormalPDF : Integrable (fun x : ℝ => x * standardNormalPDF x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hi using 1
  ext x
  rw [standardNormalPDF_eq]
  rw [show -(1/2 : ℝ)*x^2 = -x^2/2 by ring]
  ring

lemma integral_mul_standardNormalPDF_Ioi (x : ℝ) :
    (∫ y in Ioi x, y * standardNormalPDF y) = standardNormalPDF x := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y (_ : y ∈ Ici x) => (hasDerivAt_standardNormalPDF y).neg)
    (by simpa only [neg_mul, neg_neg] using
      integrable_mul_standardNormalPDF.integrableOn (s := Ioi x))
    tendsto_standardNormalPDF_atTop.neg
  simpa only [neg_neg, neg_mul, sub_neg_eq_add, zero_add, neg_zero] using hi

lemma standardNormalUpperTail_le_mills {x : ℝ} (hx : 0 < x) :
    standardNormalUpperTail x ≤ standardNormalPDF x / x := by
  apply (le_div_iff₀ hx).mpr
  rw [mul_comm, standardNormalUpperTail_eq_integral, ← integral_const_mul,
    ← integral_mul_standardNormalPDF_Ioi x]
  apply setIntegral_mono_on
    (integrable_standardNormalPDF.integrableOn.const_mul x)
    integrable_mul_standardNormalPDF.integrableOn measurableSet_Ioi
  intro y hy
  exact mul_le_mul_of_nonneg_right hy.le (standardNormalPDF_nonneg y)

lemma integrable_standardNormalPDF_div_sq_Ioi {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => standardNormalPDF y / y^2) (Ioi x) := by
  apply (integrable_standardNormalPDF.integrableOn.div_const (x^2)).mono'
    ((continuous_standardNormalPDF.measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (standardNormalPDF_nonneg y) (sq_nonneg y))]
  apply div_le_div_of_nonneg_left (standardNormalPDF_nonneg y) (sq_pos_of_pos hx)
  nlinarith [hy.out]

lemma integral_standardNormalPDF_div_sq_Ioi {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioi x, standardNormalPDF y / y^2) =
      standardNormalPDF x / x - standardNormalUpperTail x := by
  have hderiv : ∀ y ∈ Ici x, HasDerivAt (fun y => standardNormalPDF y / y)
      (-standardNormalPDF y - standardNormalPDF y / y^2) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le hx hy)
    convert (hasDerivAt_standardNormalPDF y).div (hasDerivAt_id y) hy0 using 1
    field_simp
    ring
  have hlim : Tendsto (fun y => standardNormalPDF y / y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_standardNormalPDF_atTop.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_standardNormalPDF.integrableOn.neg.sub
      (integrable_standardNormalPDF_div_sq_Ioi hx)) hlim
  have hsplit : (∫ y in Ioi x, -standardNormalPDF y - standardNormalPDF y / y^2) =
      -(∫ y in Ioi x, standardNormalPDF y) -
        (∫ y in Ioi x, standardNormalPDF y / y^2) := by
    exact (integral_sub integrable_standardNormalPDF.integrableOn.neg
      (integrable_standardNormalPDF_div_sq_Ioi hx)).trans
        (by simp only [Pi.neg_apply, integral_neg])
  rw [hsplit, ← standardNormalUpperTail_eq_integral] at hi
  linarith

lemma mills_le_standardNormalUpperTail {x : ℝ} (hx : 0 < x) :
    standardNormalPDF x * x / (x^2 + 1) ≤ standardNormalUpperTail x := by
  have hi : (∫ y in Ioi x, standardNormalPDF y / y^2) ≤
      standardNormalUpperTail x / x^2 := by
    rw [standardNormalUpperTail_eq_integral, ← integral_div]
    apply setIntegral_mono_on (integrable_standardNormalPDF_div_sq_Ioi hx)
      (integrable_standardNormalPDF.integrableOn.div_const (x^2)) measurableSet_Ioi
    intro y hy
    apply div_le_div_of_nonneg_left (standardNormalPDF_nonneg y) (sq_pos_of_pos hx)
    nlinarith [hy.out]
  rw [integral_standardNormalPDF_div_sq_Ioi hx] at hi
  apply (div_le_iff₀ (by positivity : 0 < x^2+1)).mpr
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  have ha : standardNormalPDF x / x ≤
      standardNormalUpperTail x * (x^2+1) / x^2 := by
    calc
      _ ≤ standardNormalUpperTail x / x^2 + standardNormalUpperTail x := by linarith
      _ = _ := by field_simp; ring
  have hb := (div_le_div_iff₀ hx hx2).mp ha
  apply (mul_le_mul_right hx).mp
  nlinarith

end RectangleCLT.Companion

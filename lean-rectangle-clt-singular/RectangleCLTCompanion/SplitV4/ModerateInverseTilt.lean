import RectangleCLTCompanion.SplitV4.ModerateArrayCumulants
import Mathlib.Topology.Order.IntermediateValue

/-! The inverse tilt for arbitrary bounded independent scalar arrays. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

 def moderateTaylorConstant : ℝ := 7 * Real.exp 4

theorem moderateTaylorConstant_ge_one : 1 ≤ moderateTaylorConstant := by
  have he := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 4)
  unfold moderateTaylorConstant
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {η : Fin n → Ω → ℝ} {δ : ℝ}

theorem moderateArray_local_taylor (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) (hsmall : δ * t ≤ 2) :
    |moderateArrayCGF μ η t - t ^ 2 / 2 - moderateArrayGamma μ η * t ^ 3 / 6| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 4 ∧
    |moderateArrayMean μ η t - t - moderateArrayGamma μ η * t ^ 2 / 2| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 3 ∧
    |moderateArrayVariance μ η t - 1 - moderateArrayGamma μ η * t| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 2 := by
  have he : Real.exp (2 * t * δ) ≤ Real.exp 4 := Real.exp_le_exp.mpr (by nlinarith)
  have hcoef : moderateArrayFourthBound δ t ≤ moderateTaylorConstant * δ ^ 2 := by
    unfold moderateArrayFourthBound moderateTaylorConstant
    nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 7 * δ ^ 2 by positivity)]
  refine ⟨(moderateArrayCGF_cubic hη hδ hbound hc hv ht).trans ?_,
    (moderateArrayMean_quadratic hη hδ hbound hc hv ht).trans ?_,
    (moderateArrayVariance_linear hη hδ hbound hc hv ht).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  · exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  · exact mul_le_mul_of_nonneg_right hcoef (by positivity)

theorem moderateArrayMean_sub_self (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) (hsmall : δ * t ≤ 2) :
    |moderateArrayMean μ η t - t| ≤ δ * t ^ 2 / 2 + moderateTaylorConstant * δ ^ 2 * t ^ 3 := by
  have hh := (moderateArray_local_taylor hη hδ hbound hc hv ht hsmall).2.1
  have hg := moderateArrayGamma_abs_le hη hδ hbound hv
  have hg' : |moderateArrayGamma μ η * t ^ 2 / 2| ≤ δ * t ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg t)]
    norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg (sq_nonneg _)) (by norm_num)
  have hsum := (abs_add (moderateArrayMean μ η t - t - moderateArrayGamma μ η * t ^ 2 / 2)
    (moderateArrayGamma μ η * t ^ 2 / 2)).trans (add_le_add hh hg')
  convert hsum using 1 <;> ring

theorem exists_moderateArrayMean_eq (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : 100 * moderateTaylorConstant * (δ * x) ≤ 1) :
    ∃ t ∈ Icc (0 : ℝ) (2 * x), moderateArrayMean μ η t = x := by
  have hB := moderateTaylorConstant_ge_one
  have hB0 : 0 ≤ moderateTaylorConstant := zero_le_one.trans hB
  have hy0 : 0 ≤ δ * x := mul_nonneg hδ hx
  have hBy : moderateTaylorConstant * (δ * x) ≤ 1 / 100 := by nlinarith
  have hy : δ * x ≤ 1 / 100 := by nlinarith [mul_le_mul_of_nonneg_right hB hy0]
  have hy1 : δ * x ≤ 1 := by linarith
  have hBy2 : moderateTaylorConstant * (δ * x) ^ 2 ≤ 1 / 100 := by
    have hh := mul_le_mul_of_nonneg_left hy1 (mul_nonneg hB0 hy0)
    nlinarith
  have hcoef : 2 * (δ * x) + 8 * moderateTaylorConstant * (δ * x) ^ 2 ≤ 1 := by nlinarith
  have hm := moderateArrayMean_sub_self hη hδ hbound hc hv (by positivity : 0 ≤ 2 * x)
    (by nlinarith : δ * (2 * x) ≤ 2)
  have herr : δ * (2 * x) ^ 2 / 2 + moderateTaylorConstant * δ ^ 2 * (2 * x) ^ 3 ≤ x := by
    have hh := mul_le_mul_of_nonneg_right hcoef hx
    nlinarith
  have hupper : x ≤ moderateArrayMean μ η (2 * x) := by linarith [(abs_le.mp hm).1]
  have hcont : Continuous (moderateArrayMean μ η) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_moderateArrayMean hη hbound t).continuousAt)
  exact intermediate_value_Icc (by linarith) hcont.continuousOn
    ⟨by simpa only [moderateArrayMean_zero hc] using hx, hupper⟩


theorem moderateArray_local_variance_bounds (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {x t : ℝ} (hx : 0 ≤ x)
    (hsmall : 100 * moderateTaylorConstant * (δ * x) ≤ 1) (ht : t ∈ Icc (0 : ℝ) (2 * x)) :
    1 / 2 ≤ moderateArrayVariance μ η t ∧ moderateArrayVariance μ η t ≤ 2 := by
  have hB := moderateTaylorConstant_ge_one
  have hB0 : 0 ≤ moderateTaylorConstant := zero_le_one.trans hB
  have hy0 : 0 ≤ δ * x := mul_nonneg hδ hx
  have hBy : moderateTaylorConstant * (δ * x) ≤ 1 / 100 := by nlinarith
  have hy : δ * x ≤ 1 / 100 := by nlinarith [mul_le_mul_of_nonneg_right hB hy0]
  have hy1 : δ * x ≤ 1 := by linarith
  have hBy2 : moderateTaylorConstant * (δ * x) ^ 2 ≤ 1 / 100 := by
    have hh := mul_le_mul_of_nonneg_left hy1 (mul_nonneg hB0 hy0)
    nlinarith
  have hdt : δ * t ≤ 2 := by nlinarith [ht.2]
  have hrem := (moderateArray_local_taylor hη hδ hbound hc hv ht.1 hdt).2.2
  have hg := abs_le.mp (moderateArrayGamma_abs_le hη hδ hbound hv)
  have hgt : |moderateArrayGamma μ η * t| ≤ δ * t := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_right (moderateArrayGamma_abs_le hη hδ hbound hv) ht.1
  have hdt2 : moderateTaylorConstant * δ ^ 2 * t ^ 2 ≤ 4 * moderateTaylorConstant * (δ * x) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 2)
      (show 0 ≤ moderateTaylorConstant * δ ^ 2 by positivity)]
  have hsmallv : δ * t + moderateTaylorConstant * δ ^ 2 * t ^ 2 ≤ 1 / 2 := by nlinarith [ht.2]
  have ha := abs_le.mp hrem
  have hb := abs_le.mp hgt
  constructor <;> nlinarith

end
end RectangleCLT.Companion.SplitV4

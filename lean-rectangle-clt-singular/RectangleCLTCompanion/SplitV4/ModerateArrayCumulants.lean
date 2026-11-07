import RectangleCLTCompanion.SplitV4.ModerateFourthCumulant
import RectangleCLTCompanion.LowerTaylorChain

/-! Uniform cumulant calculus for independent, potentially different, bounded scalar laws.
The analytic estimates here need only the marginal laws; independence enters the tail step. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {η : Fin n → Ω → ℝ} {δ : ℝ}

def moderateArrayCGF (μ : Measure Ω) (η : Fin n → Ω → ℝ) (t : ℝ) : ℝ := ∑ i, cgf (η i) μ t

def moderateArrayMean (μ : Measure Ω) (η : Fin n → Ω → ℝ) (t : ℝ) : ℝ := ∑ i, moderateTiltMean μ (η i) t

def moderateArrayVariance (μ : Measure Ω) (η : Fin n → Ω → ℝ) (t : ℝ) : ℝ := ∑ i, moderateTiltVariance μ (η i) t

def moderateArrayThird (μ : Measure Ω) (η : Fin n → Ω → ℝ) (t : ℝ) : ℝ := ∑ i, moderateTiltThird μ (η i) t

def moderateArrayFourth (μ : Measure Ω) (η : Fin n → Ω → ℝ) (t : ℝ) : ℝ := ∑ i, moderateTiltFourthCumulant μ (η i) t

def moderateArrayGamma (μ : Measure Ω) (η : Fin n → Ω → ℝ) : ℝ := ∑ i, ∫ ω, η i ω ^ 3 ∂μ

theorem hasDerivAt_moderateArrayCGF (hη : ∀ i, Measurable (η i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (t : ℝ) :
    HasDerivAt (moderateArrayCGF μ η) (moderateArrayMean μ η t) t := by
  exact HasDerivAt.sum (fun i _ => hasDerivAt_moderateCGF (hη i) (hbound i) t)

theorem hasDerivAt_moderateArrayMean (hη : ∀ i, Measurable (η i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (t : ℝ) :
    HasDerivAt (moderateArrayMean μ η) (moderateArrayVariance μ η t) t := by
  exact HasDerivAt.sum (fun i _ => hasDerivAt_moderateTiltMean (hη i) (hbound i) t)

theorem hasDerivAt_moderateArrayVariance (hη : ∀ i, Measurable (η i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (t : ℝ) :
    HasDerivAt (moderateArrayVariance μ η) (moderateArrayThird μ η t) t := by
  exact HasDerivAt.sum (fun i _ => hasDerivAt_moderateTiltVariance (hη i) (hbound i) t)

theorem hasDerivAt_moderateArrayThird (hη : ∀ i, Measurable (η i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (t : ℝ) :
    HasDerivAt (moderateArrayThird μ η) (moderateArrayFourth μ η t) t := by
  exact HasDerivAt.sum (fun i _ => hasDerivAt_moderateTiltThird (hη i) (hbound i) t)

theorem moderateArrayCGF_zero : moderateArrayCGF μ η 0 = 0 := by simp [moderateArrayCGF, cgf_zero]

theorem moderateArrayMean_zero (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0) : moderateArrayMean μ η 0 = 0 := by
  simp [moderateArrayMean, moderateTiltMean, moderateTiltMoment_zero, hc]

theorem moderateArrayVariance_zero (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) : moderateArrayVariance μ η 0 = 1 := by
  simpa [moderateArrayVariance, moderateTiltVariance, moderateTiltMean, moderateTiltMoment_zero, hc] using hv

theorem moderateArrayThird_zero (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0) :
    moderateArrayThird μ η 0 = moderateArrayGamma μ η := by
  simp [moderateArrayThird, moderateTiltThird, moderateTiltMean, moderateTiltMoment_zero, hc, moderateArrayGamma]

theorem moderateArrayVariance_exp_bounds (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) (t : ℝ) :
    Real.exp (-2 * |t| * δ) ≤ moderateArrayVariance μ η t ∧
      moderateArrayVariance μ η t ≤ Real.exp (2 * |t| * δ) := by
  have hv' : (∑ i, variance (η i) μ) = 1 := by
    simpa only [variance_def' (moderate_memLp_two (hη _) (hbound _)), hc, zero_pow (by decide : 2 ≠ 0), sub_zero] using hv
  constructor
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (moderateTiltVariance_exp_bounds (hη i) hδ (hbound i) t).1)
    simpa only [← Finset.mul_sum, hv', mul_one, moderateArrayVariance] using hh
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (moderateTiltVariance_exp_bounds (hη i) hδ (hbound i) t).2)
    simpa only [← Finset.mul_sum, hv', mul_one, moderateArrayVariance] using hh

theorem moderateArrayFourth_abs_le (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) (t : ℝ) :
    |moderateArrayFourth μ η t| ≤ 7 * δ ^ 2 * Real.exp (2 * |t| * δ) := by
  calc
    _ ≤ ∑ i, |moderateTiltFourthCumulant μ (η i) t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 7 * δ ^ 2 * moderateTiltVariance μ (η i) t :=
      Finset.sum_le_sum (fun i _ => moderateTiltFourthCumulant_abs_le (hη i) hδ (hbound i) t)
    _ = 7 * δ ^ 2 * moderateArrayVariance μ η t := by rw [moderateArrayVariance, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (moderateArrayVariance_exp_bounds hη hδ hbound hc hv t).2 (by positivity)

theorem moderateArrayCGF_cubic (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayCGF μ η t - t ^ 2 / 2 - moderateArrayGamma μ η * t ^ 3 / 6| ≤
      (7 * δ ^ 2 * Real.exp (2 * t * δ)) * t ^ 4 := by
  have hh := lower_taylor_chain_cubic ht (by positivity : 0 ≤ 7 * δ ^ 2 * Real.exp (2 * t * δ))
    (hasDerivAt_moderateArrayCGF hη hbound) (hasDerivAt_moderateArrayMean hη hbound)
    (hasDerivAt_moderateArrayVariance hη hbound) (hasDerivAt_moderateArrayThird hη hbound)
    (fun u hu => (moderateArrayFourth_abs_le hη hδ hbound hc hv u).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [abs_of_nonneg hu.1]; nlinarith [hu.2])) (by positivity)))
  simpa only [moderateArrayCGF_zero, moderateArrayMean_zero hc, moderateArrayVariance_zero hc hv,
    moderateArrayThird_zero hc, zero_mul, sub_zero, one_mul] using hh


theorem moderateArrayGamma_abs_le (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) : |moderateArrayGamma μ η| ≤ δ := by
  have hi (i : Fin n) : |∫ ω, η i ω ^ 3 ∂μ| ≤ δ * (∫ ω, η i ω ^ 2 ∂μ) := by
    apply (abs_integral_le_integral_abs).trans
    rw [← integral_const_mul]
    apply integral_mono_ae (moderate_integrable_pow (hη i) hδ (hbound i) 3).abs
      ((moderate_integrable_pow (hη i) hδ (hbound i) 2).const_mul δ)
    filter_upwards [hbound i] with ω hω
    change |η i ω ^ 3| ≤ δ * η i ω ^ 2
    calc
      _ = |η i ω| * (η i ω) ^ 2 := by rw [abs_pow, ← sq_abs (η i ω)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hω (sq_nonneg _)
  calc
    _ ≤ ∑ i, |∫ ω, η i ω ^ 3 ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, δ * (∫ ω, η i ω ^ 2 ∂μ) := Finset.sum_le_sum (fun i _ => hi i)
    _ = δ := by rw [← Finset.mul_sum, hv, mul_one]

def moderateArrayFourthBound (δ t : ℝ) : ℝ := 7 * δ ^ 2 * Real.exp (2 * t * δ)

theorem moderateArrayFourthBound_mono (hδ : 0 ≤ δ) {u t : ℝ} (hut : u ≤ t) :
    moderateArrayFourthBound δ u ≤ moderateArrayFourthBound δ t := by
  unfold moderateArrayFourthBound
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

theorem moderateArrayThird_difference (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayThird μ η t - moderateArrayGamma μ η| ≤ moderateArrayFourthBound δ t * t := by
  have hh := lower_meanvalue_bound ht (hasDerivAt_moderateArrayThird hη hbound)
    (fun u hu => (moderateArrayFourth_abs_le hη hδ hbound hc hv u).trans
      (by rw [abs_of_nonneg hu.1]; exact moderateArrayFourthBound_mono hδ hu.2))
  simpa only [moderateArrayThird_zero hc] using hh

theorem moderateArrayVariance_linear (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayVariance μ η t - 1 - moderateArrayGamma μ η * t| ≤
      moderateArrayFourthBound δ t * t ^ 2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun u => moderateArrayVariance μ η u - 1 - moderateArrayGamma μ η * u)
      (moderateArrayThird μ η u - moderateArrayGamma μ η) u := by
    simpa only [mul_one] using ((hasDerivAt_moderateArrayVariance hη hbound u).sub_const 1).sub
      ((hasDerivAt_id u).const_mul (moderateArrayGamma μ η))
  have hh := lower_meanvalue_bound ht hd (fun u hu =>
    (moderateArrayThird_difference hη hδ hbound hc hv hu.1).trans
      (mul_le_mul (moderateArrayFourthBound_mono hδ hu.2) hu.2 hu.1 (by unfold moderateArrayFourthBound; positivity)))
  simp only [moderateArrayVariance_zero hc hv, sub_self, mul_zero, sub_zero] at hh
  convert hh using 1 <;> ring

theorem moderateArrayMean_quadratic (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayMean μ η t - t - moderateArrayGamma μ η * t ^ 2 / 2| ≤
      moderateArrayFourthBound δ t * t ^ 3 := by
  have hd (u : ℝ) : HasDerivAt
      (fun u => moderateArrayMean μ η u - u - moderateArrayGamma μ η * u ^ 2 / 2)
      (moderateArrayVariance μ η u - 1 - moderateArrayGamma μ η * u) u := by
    have hh := ((hasDerivAt_moderateArrayMean hη hbound u).sub (hasDerivAt_id u)).sub
      (((hasDerivAt_id u).pow 2).const_mul (moderateArrayGamma μ η) |>.div_const 2)
    simp only [id_eq] at hh
    convert hh using 1 <;> ring
  have hh := lower_meanvalue_bound ht hd (fun u hu =>
    (moderateArrayVariance_linear hη hδ hbound hc hv hu.1).trans
      (mul_le_mul (moderateArrayFourthBound_mono hδ hu.2)
        (pow_le_pow_left₀ hu.1 hu.2 2) (sq_nonneg u) (by unfold moderateArrayFourthBound; positivity)))
  simp only [moderateArrayMean_zero hc, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, sub_self] at hh
  convert hh using 1 <;> ring

end
end RectangleCLT.Companion.SplitV4

import RectangleCLTCompanion.SplitV4.Printed.LowerModerateArray

/-! Literal F.1 cumulant/Taylor/inverse-root chain, using the two-copy
variance bounds. The local interval delta*t<=1 permits B=7exp4. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {η : Fin n→Ω→ℝ} {δ : ℝ}

theorem moderateArrayVariance_exp_bounds_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) (t : ℝ) :
    Real.exp (-4 * |t| * δ) ≤ moderateArrayVariance μ η t ∧
      moderateArrayVariance μ η t ≤ Real.exp (4 * |t| * δ) := by
  have hv' : (∑ i, variance (η i) μ) = 1 := by
    simpa only [variance_def' (moderate_memLp_two (hη _) (hbound _)), hc, zero_pow (by decide : 2 ≠ 0), sub_zero] using hv
  constructor
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (moderateTiltVariance_printed_copy_bounds (hη i) hδ (hbound i) t).1)
    simpa only [← Finset.mul_sum, hv', mul_one, moderateArrayVariance] using hh
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (moderateTiltVariance_printed_copy_bounds (hη i) hδ (hbound i) t).2)
    simpa only [← Finset.mul_sum, hv', mul_one, moderateArrayVariance] using hh

theorem moderateArrayFourth_abs_le_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) (t : ℝ) :
    |moderateArrayFourth μ η t| ≤ 7 * δ ^ 2 * Real.exp (4 * |t| * δ) := by
  calc
    _ ≤ ∑ i, |moderateTiltFourthCumulant μ (η i) t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 7 * δ ^ 2 * moderateTiltVariance μ (η i) t :=
      Finset.sum_le_sum (fun i _ => moderateTiltFourthCumulant_abs_le (hη i) hδ (hbound i) t)
    _ = 7 * δ ^ 2 * moderateArrayVariance μ η t := by rw [moderateArrayVariance, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (moderateArrayVariance_exp_bounds_printed hη hδ hbound hc hv t).2 (by positivity)

theorem moderateArrayCGF_cubic_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayCGF μ η t - t ^ 2 / 2 - moderateArrayGamma μ η * t ^ 3 / 6| ≤
      (7 * δ ^ 2 * Real.exp (4 * t * δ)) * t ^ 4 := by
  have hh := lower_taylor_chain_cubic ht (by positivity : 0 ≤ 7 * δ ^ 2 * Real.exp (4 * t * δ))
    (hasDerivAt_moderateArrayCGF hη hbound) (hasDerivAt_moderateArrayMean hη hbound)
    (hasDerivAt_moderateArrayVariance hη hbound) (hasDerivAt_moderateArrayThird hη hbound)
    (fun u hu => (moderateArrayFourth_abs_le_printed hη hδ hbound hc hv u).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [abs_of_nonneg hu.1]; nlinarith [hu.2])) (by positivity)))
  simpa only [moderateArrayCGF_zero, moderateArrayMean_zero hc, moderateArrayVariance_zero hc hv,
    moderateArrayThird_zero hc, zero_mul, sub_zero, one_mul] using hh


def moderateArrayFourthBound_printed (δ t : ℝ) : ℝ := 7 * δ ^ 2 * Real.exp (4 * t * δ)

theorem moderateArrayFourthBound_mono_printed (hδ : 0 ≤ δ) {u t : ℝ} (hut : u ≤ t) :
    moderateArrayFourthBound_printed δ u ≤ moderateArrayFourthBound_printed δ t := by
  unfold moderateArrayFourthBound_printed
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

theorem moderateArrayThird_difference_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayThird μ η t - moderateArrayGamma μ η| ≤ moderateArrayFourthBound_printed δ t * t := by
  have hh := lower_meanvalue_bound ht (hasDerivAt_moderateArrayThird hη hbound)
    (fun u hu => (moderateArrayFourth_abs_le_printed hη hδ hbound hc hv u).trans
      (by rw [abs_of_nonneg hu.1]; exact moderateArrayFourthBound_mono_printed hδ hu.2))
  simpa only [moderateArrayThird_zero hc] using hh

theorem moderateArrayVariance_linear_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayVariance μ η t - 1 - moderateArrayGamma μ η * t| ≤
      moderateArrayFourthBound_printed δ t * t ^ 2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun u => moderateArrayVariance μ η u - 1 - moderateArrayGamma μ η * u)
      (moderateArrayThird μ η u - moderateArrayGamma μ η) u := by
    simpa only [mul_one] using ((hasDerivAt_moderateArrayVariance hη hbound u).sub_const 1).sub
      ((hasDerivAt_id u).const_mul (moderateArrayGamma μ η))
  have hh := lower_meanvalue_bound ht hd (fun u hu =>
    (moderateArrayThird_difference_printed hη hδ hbound hc hv hu.1).trans
      (mul_le_mul (moderateArrayFourthBound_mono_printed hδ hu.2) hu.2 hu.1 (by unfold moderateArrayFourthBound_printed; positivity)))
  simp only [moderateArrayVariance_zero hc hv, sub_self, mul_zero, sub_zero] at hh
  convert hh using 1 <;> ring

theorem moderateArrayMean_quadratic_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) :
    |moderateArrayMean μ η t - t - moderateArrayGamma μ η * t ^ 2 / 2| ≤
      moderateArrayFourthBound_printed δ t * t ^ 3 := by
  have hd (u : ℝ) : HasDerivAt
      (fun u => moderateArrayMean μ η u - u - moderateArrayGamma μ η * u ^ 2 / 2)
      (moderateArrayVariance μ η u - 1 - moderateArrayGamma μ η * u) u := by
    have hh := ((hasDerivAt_moderateArrayMean hη hbound u).sub (hasDerivAt_id u)).sub
      (((hasDerivAt_id u).pow 2).const_mul (moderateArrayGamma μ η) |>.div_const 2)
    simp only [id_eq] at hh
    convert hh using 1 <;> ring
  have hh := lower_meanvalue_bound ht hd (fun u hu =>
    (moderateArrayVariance_linear_printed hη hδ hbound hc hv hu.1).trans
      (mul_le_mul (moderateArrayFourthBound_mono_printed hδ hu.2)
        (pow_le_pow_left₀ hu.1 hu.2 2) (sq_nonneg u) (by unfold moderateArrayFourthBound_printed; positivity)))
  simp only [moderateArrayMean_zero hc, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, sub_self] at hh
  convert hh using 1 <;> ring

theorem moderateArray_local_taylor_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) (hsmall : δ * t ≤ 1) :
    |moderateArrayCGF μ η t - t ^ 2 / 2 - moderateArrayGamma μ η * t ^ 3 / 6| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 4 ∧
    |moderateArrayMean μ η t - t - moderateArrayGamma μ η * t ^ 2 / 2| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 3 ∧
    |moderateArrayVariance μ η t - 1 - moderateArrayGamma μ η * t| ≤
      moderateTaylorConstant * δ ^ 2 * t ^ 2 := by
  have he : Real.exp (4 * t * δ) ≤ Real.exp 4 := Real.exp_le_exp.mpr (by nlinarith)
  have hcoef : moderateArrayFourthBound_printed δ t ≤ moderateTaylorConstant * δ ^ 2 := by
    unfold moderateArrayFourthBound_printed moderateTaylorConstant
    nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 7 * δ ^ 2 by positivity)]
  refine ⟨(moderateArrayCGF_cubic_printed hη hδ hbound hc hv ht).trans ?_,
    (moderateArrayMean_quadratic_printed hη hδ hbound hc hv ht).trans ?_,
    (moderateArrayVariance_linear_printed hη hδ hbound hc hv ht).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  · exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  · exact mul_le_mul_of_nonneg_right hcoef (by positivity)

theorem moderateArrayMean_sub_self_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {t : ℝ} (ht : 0 ≤ t) (hsmall : δ * t ≤ 1) :
    |moderateArrayMean μ η t - t| ≤ δ * t ^ 2 / 2 + moderateTaylorConstant * δ ^ 2 * t ^ 3 := by
  have hh := (moderateArray_local_taylor_printed hη hδ hbound hc hv ht hsmall).2.1
  have hg := moderateArrayGamma_abs_le hη hδ hbound hv
  have hg' : |moderateArrayGamma μ η * t ^ 2 / 2| ≤ δ * t ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg t)]
    norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg (sq_nonneg _)) (by norm_num)
  have hsum := (abs_add (moderateArrayMean μ η t - t - moderateArrayGamma μ η * t ^ 2 / 2)
    (moderateArrayGamma μ η * t ^ 2 / 2)).trans (add_le_add hh hg')
  convert hsum using 1 <;> ring

theorem exists_moderateArrayMean_eq_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
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
  have hm := moderateArrayMean_sub_self_printed hη hδ hbound hc hv (by positivity : 0 ≤ 2 * x)
    (by nlinarith : δ * (2 * x) ≤ 1)
  have herr : δ * (2 * x) ^ 2 / 2 + moderateTaylorConstant * δ ^ 2 * (2 * x) ^ 3 ≤ x := by
    have hh := mul_le_mul_of_nonneg_right hcoef hx
    nlinarith
  have hupper : x ≤ moderateArrayMean μ η (2 * x) := by linarith [(abs_le.mp hm).1]
  have hcont : Continuous (moderateArrayMean μ η) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_moderateArrayMean hη hbound t).continuousAt)
  exact intermediate_value_Icc (by linarith) hcont.continuousOn
    ⟨by simpa only [moderateArrayMean_zero hc] using hx, hupper⟩


theorem moderateArray_local_variance_bounds_printed (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
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
  have hdt : δ * t ≤ 1 := by nlinarith [ht.2]
  have hrem := (moderateArray_local_taylor_printed hη hδ hbound hc hv ht.1 hdt).2.2
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

theorem moderateArrayMean_strictMono_printed (hη : ∀i,Measurable (η i)) (hδ : 0≤δ)
    (hb : ∀i,∀ᵐ ω ∂μ,|η i ω|≤δ) (hc : ∀i,(∫ω,η i ω ∂μ)=0)
    (hv : (∑i,∫ω,η i ω^2 ∂μ)=1) : StrictMono (moderateArrayMean μ η) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_moderateArrayMean hη hb t).deriv]
  exact (Real.exp_pos (-4*|t| *δ)).trans_le (moderateArrayVariance_exp_bounds_printed hη hδ hb hc hv t).1

theorem existsUnique_moderateArrayMean_eq_printed (hη : ∀i,Measurable (η i)) (hδ : 0≤δ)
    (hb : ∀i,∀ᵐ ω ∂μ,|η i ω|≤δ) (hc : ∀i,(∫ω,η i ω ∂μ)=0)
    (hv : (∑i,∫ω,η i ω^2 ∂μ)=1) {x : ℝ} (hx : 0≤x)
    (hsmall : 100*moderateTaylorConstant*(δ*x)≤1) :
    ∃!t,t∈Icc (0:ℝ) (2*x) ∧ moderateArrayMean μ η t=x := by
  obtain ⟨t,ht,he⟩ := exists_moderateArrayMean_eq_printed hη hδ hb hc hv hx hsmall
  refine ⟨t,⟨ht,he⟩,?_⟩
  intro y hy
  exact (moderateArrayMean_strictMono_printed hη hδ hb hc hv).injective (hy.2.trans he.symm)

/-- The root also lies in the literal printed a0/delta interval, with
a0=1/10; strict monotonicity supplies uniqueness on that interval. -/
theorem existsUnique_moderateArrayMean_printed_interval (hη : ∀i,Measurable (η i)) (hδ : 0<δ)
    (hb : ∀i,∀ᵐ ω ∂μ,|η i ω|≤δ) (hc : ∀i,(∫ω,η i ω ∂μ)=0)
    (hv : (∑i,∫ω,η i ω^2 ∂μ)=1) {x : ℝ} (hx : 0≤x)
    (hsmall : 100*moderateTaylorConstant*(δ*x)≤1) :
    ∃!t,t∈Ico (0:ℝ) ((1/10:ℝ)/δ) ∧ moderateArrayMean μ η t=x := by
  obtain ⟨t,ht,he⟩ := exists_moderateArrayMean_eq_printed hη hδ.le hb hc hv hx hsmall
  have hB := moderateTaylorConstant_ge_one
  have hy : δ*x≤1/100 := by
    nlinarith [mul_le_mul_of_nonneg_right hB (mul_nonneg hδ.le hx)]
  have hupper : t<(1/10:ℝ)/δ := (lt_div_iff₀ hδ).mpr (by nlinarith [ht.2])
  refine ⟨t,⟨⟨ht.1,hupper⟩,he⟩,?_⟩
  intro y hy
  exact (moderateArrayMean_strictMono_printed hη hδ.le hb hc hv).injective (hy.2.trans he.symm)

end
end RectangleCLT.Companion.SplitV4.Printed

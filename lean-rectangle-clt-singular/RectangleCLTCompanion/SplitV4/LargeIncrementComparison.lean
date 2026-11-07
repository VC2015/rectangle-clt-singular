import RectangleCLTCompanion.SplitV4.TimeWeights
import RectangleCLTCompanion.SplitV4.SmootherC4
import RectangleCLTCompanion.SplitV4.SlepianDerivative
import RectangleCLTCompanion.SplitV4.ProductConditional
import RectangleCLTCompanion.SplitV4.ConditionalMatrixFluctuation
import RectangleCLTCompanion.SplitV4.PairedTailBudgets
import RectangleCLTCompanion.SplitV4.GaussianDerivativeContractions
import RectangleCLTCompanion.SplitV4.ArraySlepian
import RectangleCLTCompanion.SplitV4.GaussianRemainder
import RectangleCLTCompanion.SplitV4.LargeIncrementBudgets
import RectangleCLTCompanion.SplitV4.GaussianEndpointSmoothing
import RectangleCLTCompanion.SplitV4.PairedNormalization
import Mathlib.MeasureTheory.Function.L2Space

/-!
Integration and assembly of the logistic--Slepian comparison with large
increments. The scalar integration input below uses actual derivative
witnesses and the integrable endpoint weights; derivative bounds for the
probability interpolation are supplied separately from genuine Gaussian
averages and conditional coefficients.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- Finite genuine fourth moments supply the actual L2 contracts needed
for the conditional-copy coefficients. -/
theorem coordinate_memLp_two_of_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hfourth : Integrable (fun ω => X ω ^ 4) μ) :
    MemLp X (2 : ℝ≥0∞) μ := by
  apply (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr
  apply ((integrable_const (1 : ℝ)).add hfourth).mono' (hX.pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change X ω ^ 2 ≤ 1 + X ω ^ 4
  nlinarith [sq_nonneg (X ω ^ 2 - 1 / 2)]

def largeIncrementMatrixCost {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) : ℝ :=
  ∫ ω, matrixMaxEntryNorm (copyArrayTruncatedCovariance μ ξ ω h - A * A.transpose) ∂μ

def largeIncrementMeanCost {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (h : ℝ) : ℝ :=
  ∫ ω, ‖copyArrayLargeMean μ ξ ω h‖ ∂μ

def largeIncrementFourthCost {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (h : ℝ) : ℝ :=
  ∫ z : Ω × Ω, coordinateFourthBudget (fun i =>
    pairedTruncatedIncrement (ξ i z.1) (ξ i z.2) h) ∂μ.prod μ

theorem largeIncrementCosts_nonneg {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) :
    0 ≤ largeIncrementMatrixCost μ ξ A h ∧
    0 ≤ largeIncrementMeanCost μ ξ h ∧ 0 ≤ largeIncrementFourthCost μ ξ h := by
  refine ⟨integral_nonneg (fun ω => ?_), integral_nonneg (fun ω => norm_nonneg _),
    integral_nonneg (fun z => coordinateFourthBudget_nonneg _)⟩
  exact norm_nonneg _

def largeIncrementHessianTerm {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p) (h t : ℝ) : ℝ :=
  ∫ z, (smootherC4Test s).hessianTrace
    (copyArrayTruncatedCovariance μ ξ z.1 h - A * A.transpose)
    (C4Test.slepianPoint (sumVector ξ) t z) ∂μ.prod (gaussianLaw A)

def largeIncrementGradientTerm {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p) (h t : ℝ) : ℝ :=
  ∫ z, (smootherC4Test s).gradient (C4Test.slepianPoint (sumVector ξ) t z)
    (copyArrayLargeMean μ ξ z.1 h) ∂μ.prod (gaussianLaw A)

def largeIncrementRemainderTerm {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p) (h t : ℝ) : ℝ :=
  ∑ i, ∫ z, (smootherC4Test s).trapezoidalRemainder
    (C4Test.arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
    (C4Test.arrayCopyIncrement ξ i h z) (Real.sqrt t)
      ∂(gaussianLaw A).prod (μ.prod μ)

theorem abs_largeIncrementHessianTerm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h t : ℝ} (hh : 0 ≤ h) (ht : t < 1) :
    |largeIncrementHessianTerm μ ξ A s h t| ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * Real.sqrt (dimensionLog p / (1 - t))) *
        largeIncrementMatrixCost μ ξ A h := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hM (j k : Fin p) : Measurable (fun ω =>
      (copyArrayTruncatedCovariance μ ξ ω h - A * A.transpose) j k) :=
    (measurable_copyArrayTruncatedCovariance_entry (μ := μ) ξ hξ hh j k).sub measurable_const
  have hMi := integrable_matrixMaxEntryNorm_copyArrayTruncatedCovariance_sub_const
    (μ := μ) ξ hξ hind hh (A * A.transpose)
  exact (abs_integral_le_integral_abs).trans
    (slepian_weighted_hessian_contraction hp s μ A hdiag (sumVector ξ)
      (fun ω => copyArrayTruncatedCovariance μ ξ ω h - A * A.transpose) hW hM hMi ht)

theorem abs_largeIncrementGradientTerm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hξi : ∀ i, Integrable (ξ i) μ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h t : ℝ} (hh : 0 ≤ h) (ht : t < 1) :
    |largeIncrementGradientTerm μ ξ A s h t| ≤
      (Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p / (1 - t))) *
        largeIncrementMeanCost μ ξ h := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hb := measurable_copyArrayLargeMean μ ξ hξ h
  have hbi := (integrable_copyArrayLargeMean μ ξ hξ hξi hh).norm
  exact (abs_integral_le_integral_abs).trans
    (slepian_weighted_gradient_contraction hp s μ A hdiag (sumVector ξ)
      (fun ω => copyArrayLargeMean μ ξ ω h) hW hb hbi ht)

/-- The three exact time weights integrate to `2`, `pi`, and `4/3`.
Continuity at both endpoints and interior derivative witnesses suffice;
there is no assumed integrability of a totalized derivative. -/
theorem abs_sub_le_three_time_weights {φ D : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (D t) t)
    (a b c : ℝ)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1,
      |D t| ≤ a * gaussianTimeWeight t + b * pairedTimeWeight t + c * fourthTimeWeight t) :
    |φ 1 - φ 0| ≤ 2 * a + Real.pi * b + (4 / 3 : ℝ) * c := by
  let H : ℝ → ℝ := fun t =>
    a * gaussianTimeWeight t + b * pairedTimeWeight t + c * fourthTimeWeight t
  have ha := intervalIntegrable_gaussianTimeWeight.const_mul a
  have hb := intervalIntegrable_pairedTimeWeight.const_mul b
  have hc := intervalIntegrable_fourthTimeWeight.const_mul c
  have hi : IntervalIntegrable H volume (0 : ℝ) 1 := ha.add hb |>.add hc
  have hI : IntegrableOn H (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hi
  have hup := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hφ
    (fun t ht => (hd t ht).hasDerivWithinAt) hI
    (fun t ht => (le_abs_self _).trans (hbound t ht))
  have hlow := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hφ.neg
    (fun t ht => (hd t ht).neg.hasDerivWithinAt) hI
    (fun t ht => (neg_le_abs _).trans (hbound t ht))
  have heval : (∫ t in (0 : ℝ)..1, H t) = 2 * a + Real.pi * b + (4 / 3 : ℝ) * c := by
    have hab := intervalIntegral.integral_add ha hb
    have habc := intervalIntegral.integral_add (ha.add hb) hc
    simp only [Pi.add_apply] at hab habc
    change (∫ t in (0 : ℝ)..1, a * gaussianTimeWeight t + b * pairedTimeWeight t +
      c * fourthTimeWeight t) = _
    rw [habc, hab, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_gaussianTimeWeight,
      integral_pairedTimeWeight, integral_fourthTimeWeight]
    ring
  rw [heval] at hup hlow
  exact abs_le.mpr ⟨by linarith, hup⟩

def largeIncrementFourthConstant : ℝ :=
  75 * (Real.exp 2) ^ 5 * Real.exp (3 / 2 : ℝ)

def largeIncrementComparisonConstant : ℝ :=
  3 * Real.exp (3 / 2 : ℝ) + Real.pi * Real.exp (3 / 2 : ℝ) +
    largeIncrementFourthConstant

theorem largeIncrementFourthConstant_nonneg : 0 ≤ largeIncrementFourthConstant := by
  unfold largeIncrementFourthConstant
  positivity

theorem largeIncrementComparisonConstant_nonneg : 0 ≤ largeIncrementComparisonConstant := by
  unfold largeIncrementComparisonConstant
  exact add_nonneg (add_nonneg (by positivity) (by positivity)) largeIncrementFourthConstant_nonneg

theorem one_le_largeIncrementComparisonConstant : 1 ≤ largeIncrementComparisonConstant := by
  have hp : 0 ≤ Real.pi * Real.exp (3 / 2 : ℝ) := by positivity
  have h4 := largeIncrementFourthConstant_nonneg
  unfold largeIncrementComparisonConstant
  linarith [Real.add_one_le_exp (3 / 2 : ℝ)]

theorem integrated_three_costs_le {L h M B Q : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hM : 0 ≤ M) (hB : 0 ≤ B) (hQ : 0 ≤ Q) :
    2 * (3 * Real.exp (3 / 2 : ℝ) / (2 * h) * Real.sqrt L * M) +
      Real.pi * (Real.exp (3 / 2 : ℝ) / 2 * Real.sqrt L * B) +
      (4 / 3 : ℝ) * (largeIncrementFourthConstant / (8 * h ^ 3) * Real.sqrt L * Q) ≤
        largeIncrementComparisonConstant * Real.sqrt L * (M / h + B + Q / h ^ 3) := by
  have he : 0 ≤ Real.exp (3 / 2 : ℝ) := Real.exp_nonneg _
  have hp : 0 ≤ Real.pi * Real.exp (3 / 2 : ℝ) := by positivity
  have h4 := largeIncrementFourthConstant_nonneg
  have hc1 : 3 * Real.exp (3 / 2 : ℝ) ≤ largeIncrementComparisonConstant := by
    unfold largeIncrementComparisonConstant
    linarith
  have hc2 : Real.pi * Real.exp (3 / 2 : ℝ) / 2 ≤ largeIncrementComparisonConstant := by
    unfold largeIncrementComparisonConstant
    linarith
  have hc3 : largeIncrementFourthConstant / 6 ≤ largeIncrementComparisonConstant := by
    unfold largeIncrementComparisonConstant
    linarith
  have h1 := mul_le_mul_of_nonneg_right hc1 (mul_nonneg (Real.sqrt_nonneg L) (div_nonneg hM hh.le))
  have h2 := mul_le_mul_of_nonneg_right hc2 (mul_nonneg (Real.sqrt_nonneg L) hB)
  have h3 := mul_le_mul_of_nonneg_right hc3
    (mul_nonneg (Real.sqrt_nonneg L) (div_nonneg hQ (pow_nonneg hh.le 3)))
  have hs := add_le_add (add_le_add h1 h2) h3
  convert hs using 1 <;> field_simp <;> ring

/-- The exact Slepian coefficients produce the three integrable weights.
This scalar lemma is used after the actual conditional contractions have
been bounded; it retains the paired `-t/8` fourth-order coefficient. -/
theorem paired_derivative_three_weight_bound {H G R L h t K M B Q : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (ht : 0 < t) (ht1 : t < 1)
    (hH : |H| ≤ (3 * Real.exp (3 / 2 : ℝ) / h * Real.sqrt (L / (1 - t))) * M)
    (hG : |G| ≤ (Real.exp (3 / 2 : ℝ) * Real.sqrt (L / (1 - t))) * B)
    (hR : |R| ≤ (K * Real.sqrt (L / (1 - t)) / h ^ 3) * Q) :
    |(1 / 2 : ℝ) * H - (1 / (2 * Real.sqrt t)) * G - t / 8 * R| ≤
      (3 * Real.exp (3 / 2 : ℝ) / (2 * h) * Real.sqrt L * M) * gaussianTimeWeight t +
      (Real.exp (3 / 2 : ℝ) / 2 * Real.sqrt L * B) * pairedTimeWeight t +
      (K / (8 * h ^ 3) * Real.sqrt L * Q) * fourthTimeWeight t := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hgrad : 0 ≤ 1 / (2 * Real.sqrt t) := by positivity
  have hfourth : 0 ≤ t / 8 := by positivity
  have htriangle : |(1 / 2 : ℝ) * H - (1 / (2 * Real.sqrt t)) * G - t / 8 * R| ≤
      (1 / 2 : ℝ) * |H| + (1 / (2 * Real.sqrt t)) * |G| + t / 8 * |R| := by
    have hb := (abs_sub ((1 / 2 : ℝ) * H - (1 / (2 * Real.sqrt t)) * G) (t / 8 * R)).trans
      (add_le_add_right (abs_sub ((1 / 2 : ℝ) * H) ((1 / (2 * Real.sqrt t)) * G)) _)
    simpa only [abs_mul, abs_of_nonneg hhalf, abs_of_nonneg hgrad,
      abs_of_nonneg hfourth] using hb
  apply htriangle.trans
  have hm := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hH hhalf) (mul_le_mul_of_nonneg_left hG hgrad))
    (mul_le_mul_of_nonneg_left hR hfourth)
  apply hm.trans_eq
  rw [Real.sqrt_div hL]
  unfold gaussianTimeWeight pairedTimeWeight fourthTimeWeight
  rw [Real.sqrt_mul ht.le]
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hs1 : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr ht1)).ne'
  field_simp
  ring

theorem abs_largeIncrementRemainderTerm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h t : ℝ} (hh : 0 ≤ h) (hband : h ≤ s.bandwidth) (ht : 0 < t) (ht1 : t < 1) :
    |largeIncrementRemainderTerm μ ξ A s h t| ≤
      (largeIncrementFourthConstant * Real.sqrt (dimensionLog p / (1 - t)) / s.bandwidth ^ 3) *
        largeIncrementFourthCost μ ξ h := by
  exact pairedGaussianRemainder_le μ hp s A hdiag ξ hξ ht ht1 hh hband

/-- The actual smooth expectation comparison, before the conditional
large-increment mean is bounded by the expected maximum of the tail sum.
All three derivative estimates are proved inputs, rather than premises.
The endpoint passage uses the genuine Slepian expectation continuity. -/
theorem largeIncrement_smooth_expectation_comparison_conditional
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ μ) (hξi : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, (∫ ω, ξ i ω ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {h : ℝ} (hh : 0 ≤ h) (hband : h ≤ s.bandwidth) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ g, s.F g ∂gaussianLaw A)| ≤
      largeIncrementComparisonConstant * Real.sqrt (dimensionLog p) *
        (largeIncrementMatrixCost μ ξ A h / s.bandwidth + largeIncrementMeanCost μ ξ h +
          largeIncrementFourthCost μ ξ h / s.bandwidth ^ 3) := by
  let f := smootherC4Test s
  let φ := f.slepianExpectation μ (sumVector ξ) A
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hWi : Integrable (sumVector ξ) μ := integrable_finset_sum _ (fun i _ => hξi i)
  have hφ : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    f.continuousOn_slepianExpectation μ (sumVector ξ) hW hWi.norm A
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    f.hasDerivAt_arraySlepian μ ξ hξ hind hξi hmean A h hh ht.1 ht.2
  let a := 3 * Real.exp (3 / 2 : ℝ) / (2 * s.bandwidth) * Real.sqrt (dimensionLog p) *
    largeIncrementMatrixCost μ ξ A h
  let b := Real.exp (3 / 2 : ℝ) / 2 * Real.sqrt (dimensionLog p) * largeIncrementMeanCost μ ξ h
  let c := largeIncrementFourthConstant / (8 * s.bandwidth ^ 3) * Real.sqrt (dimensionLog p) *
    largeIncrementFourthCost μ ξ h
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt φ (deriv φ t) t := by
    change HasDerivAt (f.slepianExpectation μ (sumVector ξ) A)
      (deriv (f.slepianExpectation μ (sumVector ξ) A) t) t
    rw [(hd t ht).deriv]
    exact hd t ht
  have hbound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      |deriv φ t| ≤ a * gaussianTimeWeight t + b * pairedTimeWeight t + c * fourthTimeWeight t := by
    rw [(hd t ht).deriv]
    change |(1 / 2 : ℝ) * largeIncrementHessianTerm μ ξ A s h t -
      (1 / (2 * Real.sqrt t)) * largeIncrementGradientTerm μ ξ A s h t -
      t / 8 * largeIncrementRemainderTerm μ ξ A s h t| ≤ _
    exact paired_derivative_three_weight_bound hL s.bandwidth_pos ht.1 ht.2
      (abs_largeIncrementHessianTerm_le μ hp s ξ hξ hind A hdiag hh ht.2)
      (abs_largeIncrementGradientTerm_le μ hp s ξ hξ hξi A hdiag hh ht.2)
      (abs_largeIncrementRemainderTerm_le μ hp s ξ hξ A hdiag hh hband ht.1 ht.2)
  have htime := abs_sub_le_three_time_weights hφ hderiv a b c hbound
  obtain ⟨hM, hB, hQ⟩ := largeIncrementCosts_nonneg μ ξ A h
  have hcost := integrated_three_costs_le hL s.bandwidth_pos hM hB hQ
  have hfinal := htime.trans hcost
  simpa only [φ, C4Test.slepianExpectation_one, C4Test.slepianExpectation_zero,
    f, smootherC4Test_value] using hfinal

/-- The raw smooth-comparison estimate in the proof of G.1, with the
paper's actual expected maximum of the summed large increments. Finite
fourth moments discharge all first/L2 and centering requirements.  The
Gaussian covariance is the exact covariance of the independent sum.
Singular covariance and dependent coordinates are retained. -/
theorem largeIncrement_smooth_expectation_comparison
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ g, s.F g ∂gaussianLaw A)| ≤
      largeIncrementComparisonConstant * Real.sqrt (dimensionLog p) *
        (largeIncrementMatrixCost μ ξ A s.bandwidth / s.bandwidth +
          pairedTailExpectedMaximum μ ξ s.bandwidth +
          largeIncrementFourthCost μ ξ s.bandwidth / s.bandwidth ^ 3) := by
  have hξi (i : Fin n) : Integrable (ξ i) μ :=
    integrable_vector_of_coordinate_fourth_moments μ (ξ i) (hξ i) (hfourth i)
  have hm (i : Fin n) : (∫ ω, ξ i ω ∂μ) = 0 :=
    integral_vector_eq_zero_of_coordinate_centered μ (ξ i) (hξi i) (hcenter i)
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact hunit j
  have hraw := largeIncrement_smooth_expectation_comparison_conditional μ hp s ξ hξ hind hξi hm
    A hdiag s.bandwidth_pos.le le_rfl
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hξ i)) (hfourth i j)
  have hmean := expected_copyArrayLargeMean_norm_le_of_memLp_two μ ξ hξ hL2 s.bandwidth_pos.le
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_left hmean _) _)
    (mul_nonneg largeIncrementComparisonConstant_nonneg (Real.sqrt_nonneg _))

def largeIncrementBudgetConstant : ℝ :=
  2 * matrixFluctuationConstant + 16 * (Real.exp 1 - 1) + 1

def largeIncrementMasterConstant : ℝ :=
  gaussianSmoothingConstant * (1 + largeIncrementComparisonConstant * largeIncrementBudgetConstant)

def largeIncrementBandwidthRate (L D v M h : ℝ) : ℝ :=
  h * Real.sqrt L * L + L * Real.sqrt D / h + Real.sqrt L * D / h ^ 3 +
    Real.sqrt L * v / h + Real.sqrt L * M

def largeIncrementMasterRate (L D v M φ : ℝ) : ℝ :=
  Real.sqrt L / φ + φ * L ^ 2 * Real.sqrt D +
    φ ^ 3 * L ^ (7 / 2 : ℝ) * D + φ * L ^ (3 / 2 : ℝ) * v + Real.sqrt L * M

theorem largeIncrementBudgetConstant_nonneg : 0 ≤ largeIncrementBudgetConstant := by
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp 1]
  unfold largeIncrementBudgetConstant matrixFluctuationConstant
  positivity

private theorem log_two_mul_nat_le_dimensionLog {p : ℕ} (hp : 1 ≤ p) :
    Real.log (2 * (p : ℝ)) ≤ dimensionLog p := by
  apply Real.log_le_log
  · have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
    positivity
  · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p)

theorem largeIncrementBandwidthRate_nonneg {L D v M h : ℝ}
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hv : 0 ≤ v) (hM : 0 ≤ M) (hh : 0 < h) :
    0 ≤ largeIncrementBandwidthRate L D v M h := by
  unfold largeIncrementBandwidthRate
  positivity

theorem coefficient_budgets_le_bandwidth_rate {L D v M h T Q : ℝ}
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hv : 0 ≤ v) (hM : 0 ≤ M) (hh : 0 < h)
    (hT : T ≤ (2 * matrixFluctuationConstant) * (Real.sqrt (D * L) + h ^ 2 * L) + v / 2)
    (hQ : Q ≤ h ^ 4 * L + (16 * (Real.exp 1 - 1)) * D) :
    Real.sqrt L * (T / h + M + Q / h ^ 3) ≤
      largeIncrementBudgetConstant * largeIncrementBandwidthRate L D v M h := by
  let C := 2 * matrixFluctuationConstant
  let K := 16 * (Real.exp 1 - 1)
  have hC : 0 ≤ C := by dsimp [C, matrixFluctuationConstant]; positivity
  have hK : 0 ≤ K := by dsimp [K]; linarith [Real.add_one_le_exp 1]
  have h1 : 0 ≤ h * Real.sqrt L * L := by positivity
  have h2 : 0 ≤ L * Real.sqrt D / h := by positivity
  have h3 : 0 ≤ Real.sqrt L * D / h ^ 3 := by positivity
  have h4 : 0 ≤ Real.sqrt L * v / h := by positivity
  have h5 : 0 ≤ Real.sqrt L * M := by positivity
  have hc1 : C + 1 ≤ largeIncrementBudgetConstant := by unfold largeIncrementBudgetConstant; dsimp [C, K] at *; linarith
  have hc2 : C ≤ largeIncrementBudgetConstant := by linarith
  have hc3 : K ≤ largeIncrementBudgetConstant := by unfold largeIncrementBudgetConstant; dsimp [C, K] at *; linarith
  have hc4 : (1 / 2 : ℝ) ≤ largeIncrementBudgetConstant := by linarith
  have hc5 : (1 : ℝ) ≤ largeIncrementBudgetConstant := by linarith
  have hs := add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hc1 h1) (mul_le_mul_of_nonneg_right hc2 h2))
    (mul_le_mul_of_nonneg_right hc3 h3)) (mul_le_mul_of_nonneg_right hc4 h4))
    (mul_le_mul_of_nonneg_right hc5 h5)
  have heq : Real.sqrt L *
      (((C * (Real.sqrt (D * L) + h ^ 2 * L) + v / 2) / h) + M +
        (h ^ 4 * L + K * D) / h ^ 3) =
      (C + 1) * (h * Real.sqrt L * L) + C * (L * Real.sqrt D / h) +
        K * (Real.sqrt L * D / h ^ 3) + (1 / 2 : ℝ) * (Real.sqrt L * v / h) +
          1 * (Real.sqrt L * M) := by
    rw [Real.sqrt_mul hD]
    field_simp
    ring_nf
    simp only [Real.sq_sqrt hL]
    ring
  calc
    _ ≤ Real.sqrt L * (((C * (Real.sqrt (D * L) + h ^ 2 * L) + v / 2) / h) + M +
        (h ^ 4 * L + K * D) / h ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact add_le_add (add_le_add_right (div_le_div_of_nonneg_right hT hh.le) _)
        (div_le_div_of_nonneg_right hQ (pow_nonneg hh.le 3))
    _ = _ := heq
    _ ≤ _ := by
      convert hs using 1 <;> unfold largeIncrementBandwidthRate <;> ring

/-- Full G.1 in smoothing-bandwidth notation for the already normalized
summands. Both large-increment quantities are the actual paired-copy
budgets, and the rectangle distance is the full measurable-rectangle
supremum. No analytic comparison estimate is a hypothesis. -/
theorem largeIncrementGaussianComparison_bandwidth
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    {D h : ℝ} (hD : 0 ≤ D)
    (hbudget : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) (hh : 0 < h) :
    rectangleDistance μ (sumVector ξ) A ≤ largeIncrementMasterConstant *
      largeIncrementBandwidthRate (dimensionLog p) D
        (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact hunit j
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => ξ i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hξ i)) (hfourth i j)
  have hT : largeIncrementMatrixCost μ ξ A h ≤ (2 * matrixFluctuationConstant) *
      (Real.sqrt (D * dimensionLog p) + h ^ 2 * dimensionLog p) + pairedTailVariance μ ξ h / 2 := by
    unfold largeIncrementMatrixCost
    rw [hA]
    exact expected_copyArrayTruncatedCovariance_sub_covariance_le ξ hξ hind hp hh hD hfourth hbudget hL2 hcenter
  have hQ : largeIncrementFourthCost μ ξ h ≤ h ^ 4 * dimensionLog p +
      (16 * (Real.exp 1 - 1)) * D := by
    have hq := expected_pairedFourthBudget_le μ hp ξ hξ hind hh hD hfourth hbudget
    change largeIncrementFourthCost μ ξ h ≤ _ at hq
    apply hq.trans
    have hlog := mul_le_mul_of_nonneg_left (log_two_mul_nat_le_dimensionLog hp) (pow_nonneg hh.le 4)
    nlinarith
  have hv := pairedTailVariance_nonneg μ ξ h
  have hM : 0 ≤ pairedTailExpectedMaximum μ ξ h := integral_nonneg (fun z => norm_nonneg _)
  have hraw : smoothingDiscrepancy μ (sumVector ξ) A h hh ≤
      largeIncrementComparisonConstant * Real.sqrt (dimensionLog p) *
        (largeIncrementMatrixCost μ ξ A h / h + pairedTailExpectedMaximum μ ξ h +
          largeIncrementFourthCost μ ξ h / h ^ 3) := by
    apply (smoothingDiscrepancy_le_iff μ (sumVector ξ) hW A h hh _).mpr
    intro lo hi
    exact largeIncrement_smooth_expectation_comparison μ hp (FaceSmoother.closedBox lo hi h hh)
      ξ hξ hind hcenter hfourth hunit A hA
  have hcoeff := coefficient_budgets_le_bandwidth_rate hL hD hv hM hh hT hQ
  have hgap : smoothingDiscrepancy μ (sumVector ξ) A h hh ≤
      (largeIncrementComparisonConstant * largeIncrementBudgetConstant) *
        largeIncrementBandwidthRate (dimensionLog p) D
          (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
    apply hraw.trans
    have hc := mul_le_mul_of_nonneg_left hcoeff largeIncrementComparisonConstant_nonneg
    convert hc using 1 <;> ring
  have hfirst : h * Real.sqrt (dimensionLog p) * dimensionLog p ≤
      largeIncrementBandwidthRate (dimensionLog p) D
        (pairedTailVariance μ ξ h) (pairedTailExpectedMaximum μ ξ h) h := by
    have hn : 0 ≤ dimensionLog p * Real.sqrt D / h + Real.sqrt (dimensionLog p) * D / h ^ 3 +
        Real.sqrt (dimensionLog p) * pairedTailVariance μ ξ h / h +
        Real.sqrt (dimensionLog p) * pairedTailExpectedMaximum μ ξ h := by positivity
    unfold largeIncrementBandwidthRate
    linarith
  have hs := gaussianEndpointSmoothing hp μ (sumVector ξ) hW A hdiag h hh
  have hG : 0 ≤ gaussianSmoothingConstant := by linarith [gaussianSmoothingConstant_ge_two]
  apply hs.trans
  have hc := mul_le_mul_of_nonneg_left (add_le_add hgap hfirst) hG
  convert hc using 1 <;> unfold largeIncrementMasterConstant <;> ring

theorem one_le_largeIncrementMasterConstant : 1 ≤ largeIncrementMasterConstant := by
  have hG : 0 ≤ gaussianSmoothingConstant := by linarith [gaussianSmoothingConstant_ge_two]
  have hBC := mul_nonneg largeIncrementComparisonConstant_nonneg largeIncrementBudgetConstant_nonneg
  have hproduct := mul_nonneg hG hBC
  unfold largeIncrementMasterConstant
  nlinarith [gaussianSmoothingConstant_ge_two]

theorem bandwidthRate_inv_mul_eq_master {L D v M φ : ℝ} (hL : 0 < L) (hφ : 0 < φ) :
    largeIncrementBandwidthRate L D v M (φ * L)⁻¹ = largeIncrementMasterRate L D v M φ := by
  have h32 : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h72 : L ^ (7 / 2 : ℝ) = L ^ 3 * Real.sqrt L := by
    rw [show (7 / 2 : ℝ) = (3 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hL,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  unfold largeIncrementBandwidthRate largeIncrementMasterRate
  rw [h32, h72]
  field_simp
  ring

/-- G.1 in its displayed `phi` parametrization for normalized summands. -/
theorem largeIncrementGaussianComparison
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    {D φ : ℝ} (hD : 0 ≤ D)
    (hbudget : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) (hφ : 0 < φ) :
    rectangleDistance μ (sumVector ξ) A ≤ largeIncrementMasterConstant *
      largeIncrementMasterRate (dimensionLog p) D
        (pairedTailVariance μ ξ (φ * dimensionLog p)⁻¹)
        (pairedTailExpectedMaximum μ ξ (φ * dimensionLog p)⁻¹) φ := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hh : 0 < (φ * dimensionLog p)⁻¹ := inv_pos.mpr (mul_pos hφ hL)
  have hb := largeIncrementGaussianComparison_bandwidth μ hp ξ hξ hind hcenter hfourth
    hunit A hA hD hbudget hh
  simpa only [bandwidthRate_inv_mul_eq_master hL hφ] using hb

/-- Lemma G.1 exactly in the manuscript's original-observation normalization.
The constant is fixed before dimensions and probability models. The actual
paired increments are `(X_i' - X_i)/sqrt n`, their `v_t` and `M_t` use the
strict norm cutoff, and `deltaOne` is the exact maximum of fourth-moment
sums divided by `n^2`. No identical-law, symmetry, coordinate-independence,
rank, eigenvalue or correlation-gap assumption is introduced. -/
theorem gaussianComparisonWithLargeIncrementRemainders
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (_hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : ProbabilityTheory.iIndepFun X μ)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (hfourth : ∀ i j, Integrable (fun ω => X i ω j ^ 4) μ)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    {φ : ℝ} (hφ : 0 < φ) :
    rectangleDistance μ (normalizedObservationSum X) A ≤ largeIncrementMasterConstant *
      largeIncrementMasterRate (dimensionLog p) (deltaOne μ X)
        (pairedTailVariance μ (normalizedSummands X) (φ * dimensionLog p)⁻¹)
        (pairedTailExpectedMaximum μ (normalizedSummands X) (φ * dimensionLog p)⁻¹) φ := by
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hX i)) (hfourth i j)
  have hA' : A * A.transpose = covariance μ (sumVector (normalizedSummands X)) := by
    simpa only [sumVector_normalizedSummands] using hA
  have hb := largeIncrementGaussianComparison μ hp (normalizedSummands X)
    (normalizedSummands_measurable hX) (normalizedSummands_independent hind)
    (normalizedSummands_centered hcenter) (normalizedSummands_fourth_integrable hfourth)
    (normalizedSummands_unit_covariance hind hL2 hcenter haverage)
    A hA' (deltaOne_nonneg (μ := μ) (X := X))
    (normalizedSummands_fourth_sums_le_deltaOne (μ := μ) (X := X)) hφ
  simpa only [sumVector_normalizedSummands] using hb

end
end RectangleCLT.Companion.SplitV4

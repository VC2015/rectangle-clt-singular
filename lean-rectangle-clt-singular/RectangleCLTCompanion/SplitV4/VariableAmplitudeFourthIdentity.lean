import RectangleCLTCompanion.SplitV4.VariableAmplitudeRowTaylor
import RectangleCLTCompanion.FourthIdentityFubini

/-! Exact fourth-order restoration for the variable-amplitude path. The
same-copy row and the two independent-copy rows retain their signed scalar
kernels, and the cubic tensor is aggregated at the common full point. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.FaceSmoother
noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

def variableBernoulliSecond {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (q a : ℝ) (j k : Fin p) : ℝ :=
  (1-q)*s.convolutionSecondDerivative ν x j k +
    q*(∫ ω, s.convolutionSecondDerivative ν (x+a • T ω) j k ∂μ)

def variableBernoulliThird {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (q a : ℝ) (j k l : Fin p) : ℝ :=
  (1-q)*s.convolutionThirdDerivative ν x j k l +
    q*(∫ ω, s.convolutionThirdDerivative ν (x+a • T ω) j k l ∂μ)

def variableFourthRowB {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  q*a^2/2 * ∑ j, ∑ k, (∫ ω, T ω j*T ω k ∂μ)*
    (∫ ω, (∫ r in (0 : ℝ)..1, (1-r)*
      (∑ l, ∑ m, s.convolutionFourthDerivative ν (line x (T ω) (a*r)) j k l m * T ω l*T ω m)) ∂μ)

def variableFourthRowC {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (q a d : ℝ) : ℝ :=
  -d*q*a * ∑ j, ∑ k, ∑ l, (∫ ω, T ω j*T ω k*T ω l ∂μ)*
    (∫ ω, (∫ r in (0 : ℝ)..1,
      (∑ m, s.convolutionFourthDerivative ν (line x (T ω) (a*r)) j k l m * T ω m)) ∂μ)

theorem variableFourthRowB_eq_correction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p) (q a : ℝ) :
    s.variableFourthRowB ν μ T x q a = q/2*s.secondCommonPointCorrection ν μ T x a := by
  unfold variableFourthRowB secondCommonPointCorrection
  simp_rw [s.integral_secondDerivative_sub_eq_fourth_integral ν μ T hT hbound hc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem variableFourthRowC_eq_correction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) (x : Vector p) (q a d : ℝ) :
    s.variableFourthRowC ν μ T x q a d = -d*q*s.thirdCommonPointCorrection ν μ T x a := by
  unfold variableFourthRowC thirdCommonPointCorrection
  simp_rw [s.integral_thirdDerivative_sub_eq_fourth_integral ν μ T hT]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem variable_second_bernoulli_contraction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (x : Vector p) (q a : ℝ) :
    (∑ j, ∑ k, (∫ ω, T ω j*T ω k ∂μ)*s.variableBernoulliSecond ν μ T x q a j k) =
      s.observationSecondTerm ν μ T x + q*s.secondCommonPointCorrection ν μ T x a := by
  rw [s.observationSecondTerm_eq_tensor ν μ T hT hbound x]
  unfold variableBernoulliSecond secondCommonPointCorrection
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem variable_third_bernoulli_contraction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (x : Vector p) (q a : ℝ) :
    (∑ j, ∑ k, ∑ l, (∫ ω, T ω j*T ω k*T ω l ∂μ)*s.variableBernoulliThird ν μ T x q a j k l) =
      s.observationThirdTerm ν μ T x + q*s.thirdCommonPointCorrection ν μ T x a := by
  rw [s.observationThirdTerm_eq_tensor ν μ T hT hbound x]
  unfold variableBernoulliThird thirdCommonPointCorrection
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Common-point restoration of one row, including both independent-copy
corrections with their actual signs. -/
theorem variableRow_commonPoint_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0)
    (x : Vector p) (q a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    c*(s.translatedConvolution ν μ T x a-s.convolution ν x) +
      b*(∫ ω, ∑ j, T ω j*s.convolutionFirstDerivative ν (x+a • T ω) j ∂μ) =
      -(1/2 : ℝ)*(∑ j, ∑ k, (∫ ω, T ω j*T ω k ∂μ)*
        s.variableBernoulliSecond ν μ T x q a j k) +
      d*(∑ j, ∑ k, ∑ l, (∫ ω, T ω j*T ω k*T ω l ∂μ)*
        s.variableBernoulliThird ν μ T x q a j k l) +
      (s.variableFourthRowA ν μ T x a c b + s.variableFourthRowB ν μ T x q a +
        s.variableFourthRowC ν μ T x q a d) := by
  rw [s.variableRowTranslation_identity ν μ T hT hbound hc x a c b d h2 h3,
    s.variable_second_bernoulli_contraction ν μ T hT hbound x q a,
    s.variable_third_bernoulli_contraction ν μ T hT hbound x q a,
    s.variableFourthRowB_eq_correction ν μ T hT hbound hc x q a,
    s.variableFourthRowC_eq_correction ν μ T hT x q a d]
  ring

def variableRowOperator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (a c b : ℝ) : ℝ :=
  c*(s.translatedConvolution ν μ T x a-s.convolution ν x) +
    b*(∫ ω, ∑ j, T ω j*s.convolutionFirstDerivative ν (x+a • T ω) j ∂μ)

theorem integrable_variableBernoulliSecond_base
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T W : Ω → Vector p) (hT : Measurable T) (hW : Measurable W)
    (q a : ℝ) (j k : Fin p) :
    Integrable (fun ω => s.variableBernoulliSecond ν μ T (W ω) q a j k) μ :=
  ((integrable_bounded_test_comp μ W hW _ (s.continuous_convolutionSecondDerivative ν j k)
    _ (fun y => s.norm_convolutionSecondDerivative_le ν y j k)).const_mul (1-q)).add
    ((integrable_shifted_bounded_test_mean μ W T hW hT a _
      (s.continuous_convolutionSecondDerivative ν j k) _
      (fun y => s.norm_convolutionSecondDerivative_le ν y j k)).const_mul q)

theorem integrable_variableBernoulliThird_base
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T W : Ω → Vector p) (hT : Measurable T) (hW : Measurable W)
    (q a : ℝ) (j k l : Fin p) :
    Integrable (fun ω => s.variableBernoulliThird ν μ T (W ω) q a j k l) μ :=
  ((integrable_bounded_test_comp μ W hW _ (s.continuous_convolutionThirdDerivative_commonPoint ν j k l)
    _ (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)).const_mul (1-q)).add
    ((integrable_shifted_bounded_test_mean μ W T hW hT a _
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
      (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)).const_mul q)

theorem integrable_variableFourthRows_base
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T W : Ω → Vector p) (hT : Measurable T) (hW : Measurable W)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (q a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    Integrable (fun ω => s.variableFourthRowA ν μ T (W ω) a c b) μ ∧
      Integrable (fun ω => s.variableFourthRowB ν μ T (W ω) q a) μ ∧
      Integrable (fun ω => s.variableFourthRowC ν μ T (W ω) q a d) μ := by
  have hshift2 (j k : Fin p) := integrable_shifted_bounded_test_mean μ W T hW hT a _
    (s.continuous_convolutionSecondDerivative ν j k) _
    (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  have hbase2 (j k : Fin p) := integrable_bounded_test_comp μ W hW _
    (s.continuous_convolutionSecondDerivative ν j k) _
    (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  have hshift3 (j k l : Fin p) := integrable_shifted_bounded_test_mean μ W T hW hT a _
    (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
    (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)
  have hbase3 (j k l : Fin p) := integrable_bounded_test_comp μ W hW _
    (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
    (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)
  have hobs2 : Integrable (fun ω => s.observationSecondTerm ν μ T (W ω)) μ := by
    simp_rw [s.observationSecondTerm_eq_tensor ν μ T hT hbound]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      (hbase2 j k).const_mul _
  have hobs3 : Integrable (fun ω => s.observationThirdTerm ν μ T (W ω)) μ := by
    simp_rw [s.observationThirdTerm_eq_tensor ν μ T hT hbound]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun l _ => (hbase3 j k l).const_mul _
  have hop : Integrable (fun ω => s.variableRowOperator ν μ T (W ω) a c b) μ :=
    (((s.integrable_translatedConvolution_base ν μ T W hT hW a).sub
      (integrable_bounded_test_comp μ W hW _ (s.continuous_convolution ν) 1
        (fun y => s.norm_convolution_le_one ν y))).const_mul c).add
      ((s.integrable_observationGradient_base ν μ T W hT hW hδ hbound a).const_mul b)
  refine ⟨?_, ?_, ?_⟩
  · apply (hop.sub ((hobs2.const_mul (-(1/2 : ℝ))).add (hobs3.const_mul d))).congr
    apply ae_of_all
    intro ω
    simp only [Pi.sub_apply, Pi.add_apply, variableRowOperator]
    rw [s.variableRowTranslation_identity ν μ T hT hbound hc (W ω) a c b d h2 h3]
    ring
  · have hi : Integrable (fun ω => q/2*s.secondCommonPointCorrection ν μ T (W ω) a) μ := by
      unfold secondCommonPointCorrection
      exact (integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
        ((hshift2 j k).sub (hbase2 j k)).const_mul _).const_mul _
    simpa only [s.variableFourthRowB_eq_correction ν μ T hT hbound hc] using hi
  · have hi : Integrable (fun ω => -d*q*s.thirdCommonPointCorrection ν μ T (W ω) a) μ := by
      unfold thirdCommonPointCorrection
      exact (integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
        integrable_finset_sum _ fun l _ =>
          ((hshift3 j k l).sub (hbase3 j k l)).const_mul _).const_mul _
    simpa only [s.variableFourthRowC_eq_correction ν μ T hT] using hi

theorem integral_variableRow_commonPoint_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T W : Ω → Vector p) (hT : Measurable T) (hW : Measurable W)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (q a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    (∫ ω, s.variableRowOperator ν μ T (W ω) a c b ∂μ) =
      -(1/2 : ℝ)*(∑ j, ∑ k, (∫ z, T z j*T z k ∂μ)*
        (∫ ω, s.variableBernoulliSecond ν μ T (W ω) q a j k ∂μ)) +
      d*(∑ j, ∑ k, ∑ l, (∫ z, T z j*T z k*T z l ∂μ)*
        (∫ ω, s.variableBernoulliThird ν μ T (W ω) q a j k l ∂μ)) +
      (∫ ω, (s.variableFourthRowA ν μ T (W ω) a c b +
        s.variableFourthRowB ν μ T (W ω) q a + s.variableFourthRowC ν μ T (W ω) q a d) ∂μ) := by
  let B2 : Ω → ℝ := fun ω => ∑ j, ∑ k, (∫ z, T z j*T z k ∂μ)*
    s.variableBernoulliSecond ν μ T (W ω) q a j k
  let B3 : Ω → ℝ := fun ω => ∑ j, ∑ k, ∑ l, (∫ z, T z j*T z k*T z l ∂μ)*
    s.variableBernoulliThird ν μ T (W ω) q a j k l
  have hi2 (j k : Fin p) := s.integrable_variableBernoulliSecond_base ν μ T W hT hW q a j k
  have hi3 (j k l : Fin p) := s.integrable_variableBernoulliThird_base ν μ T W hT hW q a j k l
  have hb2 : Integrable B2 μ := integrable_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => (hi2 j k).const_mul _
  have hb3 : Integrable B3 μ := integrable_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (hi3 j k l).const_mul _
  have hiR := s.integrable_variableFourthRows_base ν μ T W hT hW hδ hbound hc q a c b d h2 h3
  have he (ω : Ω) : s.variableRowOperator ν μ T (W ω) a c b =
      -(1/2 : ℝ)*B2 ω+d*B3 ω+(s.variableFourthRowA ν μ T (W ω) a c b+
        s.variableFourthRowB ν μ T (W ω) q a+s.variableFourthRowC ν μ T (W ω) q a d) :=
    s.variableRow_commonPoint_identity ν μ T hT hbound hc (W ω) q a c b d h2 h3
  rw [integral_congr_ae (ae_of_all _ he),
    integral_add (f := fun ω => -(1/2 : ℝ)*B2 ω+d*B3 ω)
      (g := fun ω => s.variableFourthRowA ν μ T (W ω) a c b+
        s.variableFourthRowB ν μ T (W ω) q a+s.variableFourthRowC ν μ T (W ω) q a d)
      ((hb2.const_mul (-(1/2 : ℝ))).add (hb3.const_mul d)) ((hiR.1.add hiR.2.1).add hiR.2.2),
    integral_add (f := fun ω => -(1/2 : ℝ)*B2 ω) (g := fun ω => d*B3 ω)
      (hb2.const_mul (-(1/2 : ℝ))) (hb3.const_mul d), integral_const_mul, integral_const_mul]
  have e2 : (∫ ω, B2 ω ∂μ) = ∑ j, ∑ k, (∫ z, T z j*T z k ∂μ)*
      (∫ ω, s.variableBernoulliSecond ν μ T (W ω) q a j k ∂μ) := by
    unfold B2
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => (hi2 j k).const_mul _]
    simp_rw [integral_finset_sum _ fun k _ => (hi2 _ k).const_mul _, integral_const_mul]
  have e3 : (∫ ω, B3 ω ∂μ) = ∑ j, ∑ k, ∑ l, (∫ z, T z j*T z k*T z l ∂μ)*
      (∫ ω, s.variableBernoulliThird ν μ T (W ω) q a j k l ∂μ) := by
    unfold B3
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun l _ => (hi3 j k l).const_mul _]
    simp_rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      (hi3 _ k l).const_mul _, integral_finset_sum _ fun l _ => (hi3 _ _ l).const_mul _, integral_const_mul]
  rw [e2, e3]

private theorem variable_weighted_three {α : Type*} [Fintype α]
    (w f g r : α → ℝ) (c d : ℝ) :
    (∑ z, w z*(c*f z+d*g z+r z)) =
      c*(∑ z, w z*f z)+d*(∑ z, w z*g z)+∑ z, w z*r z := by
  calc
    _ = ∑ z, (c*(w z*f z)+d*(w z*g z)+w z*r z) := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem variable_weighted_second {α : Type*} [Fintype α]
    (w : α → ℝ) (M : Fin p → Fin p → ℝ) (D : α → Fin p → Fin p → ℝ) :
    (∑ z, w z*∑ j, ∑ k, M j k*D z j k) =
      ∑ j, ∑ k, M j k*∑ z, w z*D z j k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem variable_weighted_third {α : Type*} [Fintype α]
    (w : α → ℝ) (M : Fin p → Fin p → Fin p → ℝ)
    (D : α → Fin p → Fin p → Fin p → ℝ) :
    (∑ z, w z*∑ j, ∑ k, ∑ l, M j k l*D z j k l) =
      ∑ j, ∑ k, ∑ l, M j k l*∑ z, w z*D z j k l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro z _
  ring

def variableSelectorFourthRemainder {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a c b d : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    (∫ ω, (s.variableFourthRowA ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b +
      s.variableFourthRowB ν μ (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a +
      s.variableFourthRowC ν μ (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a d) ∂μ)

theorem variable_row_mask_commonPoint_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (x : Vector p) (q a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    (∑ mask : Kane.Cube n, Kane.maskWeight q mask *
      (∫ ω, s.variableRowOperator ν μ (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ)) =
      -(1/2 : ℝ)*(∑ j, ∑ k, (∫ ω, ξ i ω j*ξ i ω k ∂μ)*
        s.selectorSecondDerivativeAverage ν μ ξ x q a j k) +
      d*(∑ j, ∑ k, ∑ l, (∫ ω, ξ i ω j*ξ i ω k*ξ i ω l ∂μ)*
        s.selectorThirdDerivativeAverage ν μ ξ x q a j k l) +
      ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
        (∫ ω, (s.variableFourthRowA ν μ (ξ i)
          (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b+
          s.variableFourthRowB ν μ (ξ i)
            (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a+
          s.variableFourthRowC ν μ (ξ i)
            (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a d) ∂μ) := by
  let W : Kane.Cube n → Ω → Vector p := fun mask ω =>
    x+a • maskObservationSum ξ (Function.update mask i false) ω
  let M2 := fun j k => ∫ ω, ξ i ω j*ξ i ω k ∂μ
  let M3 := fun j k l => ∫ ω, ξ i ω j*ξ i ω k*ξ i ω l ∂μ
  let D2 := fun mask j k => ∫ ω, s.variableBernoulliSecond ν μ (ξ i) (W mask ω) q a j k ∂μ
  let D3 := fun mask j k l => ∫ ω, s.variableBernoulliThird ν μ (ξ i) (W mask ω) q a j k l ∂μ
  let R := fun mask => ∫ ω, (s.variableFourthRowA ν μ (ξ i) (W mask ω) a c b+
    s.variableFourthRowB ν μ (ξ i) (W mask ω) q a+s.variableFourthRowC ν μ (ξ i) (W mask ω) q a d) ∂μ
  have hw (mask : Kane.Cube n) : Measurable (W mask) :=
    measurable_const.add (measurable_const.smul
      (measurable_maskObservationSum ξ h.measurable (Function.update mask i false)))
  have he (mask : Kane.Cube n) :
      (∫ ω, s.variableRowOperator ν μ (ξ i) (W mask ω) a c b ∂μ) =
        -(1/2 : ℝ)*(∑ j, ∑ k, M2 j k*D2 mask j k)+
          d*(∑ j, ∑ k, ∑ l, M3 j k l*D3 mask j k l)+R mask :=
    s.integral_variableRow_commonPoint_identity ν μ (ξ i) (W mask) (h.measurable i) (hw mask)
      h.delta_nonneg (h.bounded i) (h.centered i) q a c b d h2 h3
  change (∑ mask, Kane.maskWeight q mask*(∫ ω,
    s.variableRowOperator ν μ (ξ i) (W mask ω) a c b ∂μ)) = _
  simp_rw [he]
  rw [variable_weighted_three, variable_weighted_second, variable_weighted_third]
  have hc2 (j k : Fin p) : (∑ mask, Kane.maskWeight q mask*D2 mask j k) =
      s.selectorSecondDerivativeAverage ν μ ξ x q a j k :=
    sum_mask_freshCopy_average μ ξ h.measurable h.independent h.bounded i q a x
      (fun y => s.convolutionSecondDerivative ν y j k)
      (s.continuous_convolutionSecondDerivative ν j k) _
      (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  have hc3 (j k l : Fin p) : (∑ mask, Kane.maskWeight q mask*D3 mask j k l) =
      s.selectorThirdDerivativeAverage ν μ ξ x q a j k l :=
    sum_mask_freshCopy_average μ ξ h.measurable h.independent h.bounded i q a x
      (fun y => s.convolutionThirdDerivative ν y j k l)
      (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
      (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)
  simp_rw [hc2, hc3]
  rfl

omit ν [IsProbabilityMeasure ν] in
theorem variableHeatShiftExpectation_eq_convolution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) :
    s.variableHeatShiftExpectation μ V A γ ε x t =
      ∫ ω, s.convolution (gaussianLaw (Real.sqrt (t+ε) • A)) (x+γ t • V ω) ∂μ := by
  have hm : Measurable (fun z : Ω × Vector p => s.F (x+γ t • V z.1+Real.sqrt (t+ε) • z.2)) :=
    s.continuous_F.measurable.comp ((measurable_const.add
      (measurable_const.smul (hV.comp measurable_fst))).add (measurable_const.smul measurable_snd))
  have hi := (integrable_const (1 : ℝ) : Integrable (fun _ : Ω × Vector p => (1 : ℝ))
    (μ.prod (gaussianLaw A))).mono' hm.aestronglyMeasurable (ae_of_all _ fun _ => s.norm_F_le_one _)
  unfold variableHeatShiftExpectation
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  exact s.gaussianHeat_eq_convolution A (x+γ t • V ω) (t+ε)

omit ν [IsProbabilityMeasure ν] in
theorem variableHeatShiftDerivative_eq_spatial_add_heat
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) {t : ℝ} (htε : 0 < t+ε) :
    s.variableHeatShiftDerivative μ V A γ γ' ε x t =
      γ' t*(∫ ω, ∑ j, V ω j*s.convolutionFirstDerivative
        (gaussianLaw (Real.sqrt (t+ε) • A)) (x+γ t • V ω) j ∂μ) +
      (1/2 : ℝ)*∑ j, ∑ k, (A*A.transpose) j k*
        (∫ ω, s.convolutionSecondDerivative (gaussianLaw (Real.sqrt (t+ε) • A))
          (x+γ t • V ω) j k ∂μ) := by
  let ν := gaussianLaw (Real.sqrt (t+ε) • A)
  let W := fun ω => x+γ t • V ω
  have hW : Measurable W := measurable_const.add (measurable_const.smul hV)
  have hi1 (j : Fin p) := integrable_coordinate_mul_bounded_test μ V hV hδ hbound W hW j _
    (s.continuous_convolutionFirstDerivative ν j) _ (fun y => s.norm_convolutionFirstDerivative_le ν y j)
  have hi2 (j k : Fin p) := integrable_bounded_test_comp μ W hW _
    (s.continuous_convolutionSecondDerivative ν j k) _ (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  rw [s.variableHeatShiftDerivative_eq_heat μ V hV hbound A γ γ' ε x htε]
  change (∫ ω, (∑ j, (γ' t*V ω j)*s.convolutionFirstDerivative ν (W ω) j)+
    (1/2 : ℝ)*∑ j, ∑ k, (A*A.transpose) j k*s.convolutionSecondDerivative ν (W ω) j k ∂μ) = _
  have hp (ω : Ω) : (∑ j, (γ' t*V ω j)*s.convolutionFirstDerivative ν (W ω) j) =
      γ' t*(∑ j, V ω j*s.convolutionFirstDerivative ν (W ω) j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hp]
  rw [integral_add (f := fun ω => γ' t*(∑ j, V ω j*s.convolutionFirstDerivative ν (W ω) j))
      (g := fun ω => (1/2 : ℝ)*∑ j, ∑ k, (A*A.transpose) j k*s.convolutionSecondDerivative ν (W ω) j k)
      ((integrable_finset_sum _ fun j _ => hi1 j).const_mul _)
      ((integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => (hi2 j k).const_mul _).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => (hi2 j k).const_mul _]
  simp_rw [integral_finset_sum _ fun k _ => (hi2 _ k).const_mul _, integral_const_mul]
  rfl

def variableSelectorOperator {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (S : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (q a c b : ℝ) : ℝ :=
  c*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    (s.fixedSelectorValue ν μ ξ x a (Function.update mask i true)-
      s.fixedSelectorValue ν μ ξ x a (Function.update mask i false))) +
  b*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    s.fixedSelectorGradient ν μ ξ x a i (Function.update mask i true)) +
  ∑ mask : Kane.Cube n, Kane.maskWeight q mask*s.fixedSelectorHeat ν μ ξ S x a mask

omit ν [IsProbabilityMeasure ν] in
theorem variableSelectorHeatDerivative_eq_operator
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) (ε : ℝ)
    (x : Vector p) {t : ℝ} (htε : 0 < t+ε) :
    s.variableSelectorHeatDerivative μ ξ A γ γ' ε x t =
      s.variableSelectorOperator (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ (A*A.transpose) x
        (Companion.SplitV4.variableRetention γ t) (γ t)
        (Companion.SplitV4.variableRetentionDerivative γ γ' t)
        (Companion.SplitV4.variableRetention γ t*γ' t) := by
  let ν := gaussianLaw (Real.sqrt (t+ε) • A)
  let q := Companion.SplitV4.variableRetention γ t
  let a := γ t
  let c := Companion.SplitV4.variableRetentionDerivative γ γ' t
  let V := s.fixedSelectorValue ν μ ξ x a
  let G := fun i mask => s.fixedSelectorGradient ν μ ξ x a i mask
  have hvalue (mask : Kane.Cube n) :
      s.variableHeatShiftExpectation μ (maskObservationSum ξ mask) A γ ε x t = V mask :=
    s.variableHeatShiftExpectation_eq_convolution μ _ (measurable_maskObservationSum ξ h.measurable mask) A γ ε x t
  have hsplit (mask : Kane.Cube n) :
      s.variableHeatShiftDerivative μ (maskObservationSum ξ mask) A γ γ' ε x t =
        γ' t*(∑ i, if mask i then G i mask else 0)+s.fixedSelectorHeat ν μ ξ (A*A.transpose) x a mask := by
    rw [s.variableHeatShiftDerivative_eq_spatial_add_heat μ _
      (measurable_maskObservationSum ξ h.measurable mask)
      (mul_nonneg (Nat.cast_nonneg _) h.delta_nonneg)
      (maskObservationSum_bounded μ ξ h.delta_nonneg h.bounded mask) A γ γ' ε x htε,
      s.integral_maskObservationSum_gradient_eq ν μ ξ h.measurable h.delta_nonneg h.bounded]
    rfl
  unfold variableSelectorHeatDerivative variableSelectorOperator
  simp_rw [hvalue, hsplit, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hmass : (∑ mask : Kane.Cube n, selectorWeightDerivative q c mask*V mask) =
      c*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
        (V (Function.update mask i true)-V (Function.update mask i false))) := by
    simpa only [selectorWeightDerivative, BernoulliSelectorAlgebra.massDerivative,
      BernoulliSelectorAlgebra.coordinateMassDerivative, BernoulliSelectorAlgebra.weightExcept] using
      BernoulliSelectorAlgebra.mass_derivative_regroup q c V
  have hamp : (∑ mask : Kane.Cube n, Kane.maskWeight q mask*(γ' t*∑ i, if mask i then G i mask else 0)) =
      (q*γ' t)*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*G i (Function.update mask i true)) := by
    calc
      _ = γ' t*(∑ mask : Kane.Cube n, Kane.maskWeight q mask*∑ i, if mask i then G i mask else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro mask _
        ring
      _ = _ := by rw [BernoulliSelectorAlgebra.retained_amplitude_regroup]; ring
  change (∑ mask, selectorWeightDerivative q c mask*V mask)+
    ((∑ mask, Kane.maskWeight q mask*(γ' t*∑ i, if mask i then G i mask else 0))+
      ∑ mask, Kane.maskWeight q mask*s.fixedSelectorHeat ν μ ξ (A*A.transpose) x a mask) = _
  rw [hmass, hamp]
  ring

theorem variable_forced_increment_eq_rowOperator
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (mask : Kane.Cube n) (i : Fin n) (x : Vector p) (a c b : ℝ) :
    c*(s.fixedSelectorValue ν μ ξ x a (Function.update mask i true)-
      s.fixedSelectorValue ν μ ξ x a (Function.update mask i false)) +
      b*s.fixedSelectorGradient ν μ ξ x a i (Function.update mask i true) =
    ∫ ω, s.variableRowOperator ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ := by
  let W := fun ω => x+a • maskObservationSum ξ (Function.update mask i false) ω
  have hW : Measurable W := measurable_const.add
    (measurable_const.smul (measurable_maskObservationSum ξ h.measurable (Function.update mask i false)))
  have htr := s.integrable_translatedConvolution_base ν μ (ξ i) W (h.measurable i) hW a
  have hf := integrable_bounded_test_comp μ W hW _ (s.continuous_convolution ν) 1
    (fun y => s.norm_convolution_le_one ν y)
  have hg := s.integrable_observationGradient_base ν μ (ξ i) W (h.measurable i) hW
    h.delta_nonneg (h.bounded i) a
  have htrue : s.fixedSelectorValue ν μ ξ x a (Function.update mask i true) =
      ∫ ω, s.translatedConvolution ν μ (ξ i) (W ω) a ∂μ :=
    integral_mask_force_true_eq_double μ ξ h.measurable h.independent h.bounded mask i a x
      _ (s.continuous_convolution ν) 1 (fun y => s.norm_convolution_le_one ν y)
  rw [htrue, s.fixedSelectorGradient_force_true_eq_double ν μ ξ h.measurable h.independent
    h.delta_nonneg h.bounded]
  unfold variableRowOperator
  rw [integral_add
    (f := fun ω => c*(s.translatedConvolution ν μ (ξ i) (W ω) a-s.convolution ν (W ω)))
    (g := fun ω => b*(∫ ω', ∑ j, ξ i ω' j*s.convolutionFirstDerivative ν (W ω+a • ξ i ω') j ∂μ))
    ((htr.sub hf).const_mul c) (hg.const_mul b), integral_const_mul, integral_const_mul,
    integral_sub htr hf]
  rfl

private theorem variable_sum_second {n : ℕ}
    (M : Fin n → Fin p → Fin p → ℝ) (D : Fin p → Fin p → ℝ) :
    (∑ i, ∑ j, ∑ k, M i j k*D j k) = ∑ j, ∑ k, (∑ i, M i j k)*D j k := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private theorem variable_sum_third {n : ℕ}
    (M : Fin n → Fin p → Fin p → Fin p → ℝ) (D : Fin p → Fin p → Fin p → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, M i j k l*D j k l) =
      ∑ j, ∑ k, ∑ l, (∑ i, M i j k l)*D j k l := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

def variableSignedCubicPathTerm {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, (∑ i, ∫ ω, ξ i ω j*ξ i ω k*ξ i ω l ∂μ)*
    s.selectorThirdDerivativeAverage ν μ ξ x q a j k l

/-- Full finite-array identity: the signed cubic moments are summed
before contraction, and covariance cancellation is an actual conclusion. -/
theorem variableSelectorOperator_fourth_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (q a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    s.variableSelectorOperator ν μ ξ (A*A.transpose) x q a c b =
      d*s.variableSignedCubicPathTerm ν μ ξ x q a +
        s.variableSelectorFourthRemainder ν μ ξ x q a c b d := by
  let V := s.fixedSelectorValue ν μ ξ x a
  let G := fun i mask => s.fixedSelectorGradient ν μ ξ x a i mask
  let D2 := s.selectorSecondDerivativeAverage ν μ ξ x q a
  let D3 := s.selectorThirdDerivativeAverage ν μ ξ x q a
  let M2 := fun i j k => ∫ ω, ξ i ω j*ξ i ω k ∂μ
  let M3 := fun i j k l => ∫ ω, ξ i ω j*ξ i ω k*ξ i ω l ∂μ
  let R := fun i => ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    (∫ ω, (s.variableFourthRowA ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b+
      s.variableFourthRowB ν μ (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a+
      s.variableFourthRowC ν μ (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a d) ∂μ)
  have hforced : s.variableSelectorOperator ν μ ξ (A*A.transpose) x q a c b =
      (∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
        (∫ ω, s.variableRowOperator ν μ (ξ i)
          (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ)) +
        ∑ mask : Kane.Cube n, Kane.maskWeight q mask*s.fixedSelectorHeat ν μ ξ (A*A.transpose) x a mask := by
    unfold variableSelectorOperator
    calc
      _ = (∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
        (c*(V (Function.update mask i true)-V (Function.update mask i false))+
          b*G i (Function.update mask i true)))+
          ∑ mask : Kane.Cube n, Kane.maskWeight q mask*s.fixedSelectorHeat ν μ ξ (A*A.transpose) x a mask := by
        have he (i : Fin n) :
            (∑ mask : Kane.Cube n, Kane.maskWeight q mask*
              (c*(V (Function.update mask i true)-V (Function.update mask i false))+
                b*G i (Function.update mask i true))) =
            c*(∑ mask : Kane.Cube n, Kane.maskWeight q mask*
              (V (Function.update mask i true)-V (Function.update mask i false)))+
            b*(∑ mask : Kane.Cube n, Kane.maskWeight q mask*G i (Function.update mask i true)) := by
          simpa only [add_zero, mul_zero, Finset.sum_const_zero] using
            variable_weighted_three (Kane.maskWeight q)
              (fun mask => V (Function.update mask i true)-V (Function.update mask i false))
              (fun mask => G i (Function.update mask i true)) (fun _ => 0) c b
        simp_rw [he]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro mask _
        congr 1
        exact s.variable_forced_increment_eq_rowOperator ν μ ξ h mask i x a c b
  have hone (i : Fin n) :
      (∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω,
        s.variableRowOperator ν μ (ξ i) (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ)) =
        -(1/2 : ℝ)*(∑ j, ∑ k, M2 i j k*D2 j k)+
          d*(∑ j, ∑ k, ∑ l, M3 i j k l*D3 j k l)+R i :=
    s.variable_row_mask_commonPoint_identity ν μ ξ h i x q a c b d h2 h3
  rw [hforced]
  simp_rw [hone]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [variable_sum_second, variable_sum_third,
    s.sum_mask_fixedSelectorHeat_eq ν μ ξ (A*A.transpose) x q a]
  have hm (j k : Fin p) : (A*A.transpose) j k = ∑ i, M2 i j k := by
    rw [hA]
    exact h.covariance_sum j k
  simp_rw [hm]
  change -(1/2 : ℝ)*(∑ j, ∑ k, (∑ i, M2 i j k)*D2 j k)+
    d*(∑ j, ∑ k, ∑ l, (∑ i, M3 i j k l)*D3 j k l)+(∑ i, R i)+
      (1/2 : ℝ)*(∑ j, ∑ k, (∑ i, M2 i j k)*D2 j k) = _
  change _ = d*(∑ j, ∑ k, ∑ l, (∑ i, M3 i j k l)*D3 j k l)+∑ i, R i
  ring

omit ν [IsProbabilityMeasure ν] in
theorem variableSelectorHeatDerivative_fourth_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) {t : ℝ}
    (hpos : 0 < γ t) (htε : 0 < t+ε) :
    s.variableSelectorHeatDerivative μ ξ A γ γ' ε x t =
      ((-(γ t)+(1-t)*γ' t)/6)*s.variableSignedCubicPathTerm
        (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x
        (Companion.SplitV4.variableRetention γ t) (γ t) +
      s.variableSelectorFourthRemainder (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x
        (Companion.SplitV4.variableRetention γ t) (γ t)
        (Companion.SplitV4.variableRetentionDerivative γ γ' t)
        (Companion.SplitV4.variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6) := by
  rw [s.variableSelectorHeatDerivative_eq_operator μ ξ h A γ γ' ε x htε]
  apply s.variableSelectorOperator_fourth_identity _ μ ξ h A hA
  · unfold Companion.SplitV4.variableRetention Companion.SplitV4.variableRetentionDerivative
    field_simp [hpos.ne']
    <;> ring
  · unfold Companion.SplitV4.variableRetention Companion.SplitV4.variableRetentionDerivative
    field_simp [hpos.ne']
    <;> ring

omit ν [IsProbabilityMeasure ν] in
/-- General-amplitude fourth-order identity for the actual independent
finite-mask law and the actual smoother, with no derivative identity premise. -/
theorem hasDerivAt_integral_variableSeededInterpolationLaw_fourth_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < γ r)
    (hq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Companion.SplitV4.variableRetention γ r ∈ Set.Icc (0 : ℝ) 1)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hcont : ContinuousAt γ' t) :
    HasDerivAt (fun r => ∫ y, s.F (x+y)
      ∂Companion.SplitV4.variableSeededInterpolationLaw μ ξ A γ ε r)
      (((-(γ t)+(1-t)*γ' t)/6)*s.variableSignedCubicPathTerm
        (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x
        (Companion.SplitV4.variableRetention γ t) (γ t) +
       s.variableSelectorFourthRemainder (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x
        (Companion.SplitV4.variableRetention γ t) (γ t)
        (Companion.SplitV4.variableRetentionDerivative γ γ' t)
        (Companion.SplitV4.variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6)) t := by
  rw [← s.variableSelectorHeatDerivative_fourth_identity μ ξ h A hA γ γ' ε x
    (hpos t ⟨ht, ht1⟩) (by linarith)]
  exact s.hasDerivAt_integral_variableSeededInterpolationLaw μ ξ h.measurable h.delta_nonneg h.bounded
    A γ γ' hε hderiv hpos hq x ht ht1 hcont

private theorem variable_interval_sum2 (f : Fin p → Fin p → ℝ → ℝ)
    (c : Fin p → Fin p → ℝ)
    (hi : ∀ j k, IntervalIntegrable (f j k) volume 0 1) :
    (∑ j, ∑ k, c j k * (∫ r in (0 : ℝ)..1, f j k r)) =
      ∫ r in (0 : ℝ)..1, ∑ j, ∑ k, c j k * f j k r := by
  have hinner (j : Fin p) : (∑ k, c j k * (∫ r in (0 : ℝ)..1, f j k r)) =
      ∫ r in (0 : ℝ)..1, ∑ k, c j k * f j k r := by
    rw [intervalIntegral.integral_finset_sum (fun k _ => (hi j k).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  have ho := intervalIntegral.integral_finset_sum (s := Finset.univ) (fun j _ =>
    IntervalIntegrable.sum Finset.univ (fun k _ => (hi j k).const_mul (c j k)))
  simp only [Finset.sum_apply] at ho
  exact ho.symm

private theorem variable_interval_sum3 (f : Fin p → Fin p → Fin p → ℝ → ℝ)
    (c : Fin p → Fin p → Fin p → ℝ)
    (hi : ∀ j k l, IntervalIntegrable (f j k l) volume 0 1) :
    (∑ j, ∑ k, ∑ l, c j k l * (∫ r in (0 : ℝ)..1, f j k l r)) =
      ∫ r in (0 : ℝ)..1, ∑ j, ∑ k, ∑ l, c j k l * f j k l r := by
  have hinner (j : Fin p) := variable_interval_sum2 (f j) (c j) (hi j)
  simp_rw [hinner]
  have ho := intervalIntegral.integral_finset_sum (s := Finset.univ) (fun j _ =>
    IntervalIntegrable.sum Finset.univ (fun k _ =>
      IntervalIntegrable.sum Finset.univ (fun l _ => (hi j k l).const_mul (c j k l))))
  simp only [Finset.sum_apply] at ho
  exact ho.symm

private theorem variable_fourthTensor_pair_integral (x u v : Vector p) (a : ℝ) :
    (∑ j, ∑ k, (u j * u k) *
      (∫ r in (0 : ℝ)..1, (1 - r) *
        (∑ l, ∑ m, s.convolutionFourthDerivative ν
          (line x v (a * r)) j k l m * v l * v m))) =
      ∫ r in (0 : ℝ)..1, (1 - r) *
        s.convolutionFourthTensor ν (line x v (a * r)) u u v v := by
  have hc (j k l m : Fin p) :
      Continuous (fun r => s.convolutionFourthDerivative ν (line x v (a * r)) j k l m) :=
    (s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).comp
      (continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const))
  have hi (j k : Fin p) : IntervalIntegrable (fun r => (1 - r) *
      (∑ l, ∑ m, s.convolutionFourthDerivative ν
        (line x v (a * r)) j k l m * v l * v m)) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul (continuous_finset_sum _ (fun l _ =>
      continuous_finset_sum _ (fun m _ => ((hc j k l m).mul continuous_const).mul continuous_const)))).intervalIntegrable 0 1
  rw [variable_interval_sum2 (fun j k r => (1 - r) *
      (∑ l, ∑ m, s.convolutionFourthDerivative ν
        (line x v (a * r)) j k l m * v l * v m)) (fun j k => u j * u k) hi]
  apply intervalIntegral.integral_congr
  intro r _
  unfold convolutionFourthTensor
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

private theorem variable_fourthTensor_triple_integral (x u v : Vector p) (a : ℝ) :
    (∑ j, ∑ k, ∑ l, (u j * u k * u l) *
      (∫ r in (0 : ℝ)..1,
        (∑ m, s.convolutionFourthDerivative ν (line x v (a * r)) j k l m * v m))) =
      ∫ r in (0 : ℝ)..1,
        s.convolutionFourthTensor ν (line x v (a * r)) u u u v := by
  have hc (j k l m : Fin p) :
      Continuous (fun r => s.convolutionFourthDerivative ν (line x v (a * r)) j k l m) :=
    (s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).comp
      (continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const))
  have hi (j k l : Fin p) : IntervalIntegrable (fun r =>
      ∑ m, s.convolutionFourthDerivative ν (line x v (a * r)) j k l m * v m) volume 0 1 :=
    (continuous_finset_sum _ (fun m _ => (hc j k l m).mul continuous_const)).intervalIntegrable 0 1
  rw [variable_interval_sum3 (fun j k l r =>
      ∑ m, s.convolutionFourthDerivative ν (line x v (a * r)) j k l m * v m)
      (fun j k l => u j * u k * u l) hi]
  apply intervalIntegral.integral_congr
  intro r _
  unfold convolutionFourthTensor
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring


def variableFourthRowB_freshPair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  q*a^2/2 * ∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1, (1-r)*
    s.convolutionFourthTensor ν (line x (T z.2) (a*r))
      (T z.1) (T z.1) (T z.2) (T z.2)) ∂μ.prod μ

def variableFourthRowC_freshPair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Vector p) (x : Vector p) (q a d : ℝ) : ℝ :=
  -d*q*a * ∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1,
    s.convolutionFourthTensor ν (line x (T z.2) (a*r))
      (T z.1) (T z.1) (T z.1) (T z.2)) ∂μ.prod μ

theorem variableFourthRowB_eq_freshPair
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (x : Vector p) (q : ℝ) {a : ℝ} (ha : a ≠ 0) :
    s.variableFourthRowB ν μ T x q a = s.variableFourthRowB_freshPair ν μ T x q a := by
  have hi (j k : Fin p) : Integrable (fun ω => T ω j*T ω k) μ := by
    simpa [Fin.prod_univ_succ] using
      integrable_bounded_coordinate_product μ T hT hbound (![j,k] : Fin 2 → Fin p)
  unfold variableFourthRowB variableFourthRowB_freshPair
  congr 1
  rw [Companion.integral_fresh_pair_tensor2 μ (fun ω j k => T ω j*T ω k)
    (fun ω j k => ∫ r in (0 : ℝ)..1, (1-r)*
      (∑ l, ∑ m, s.convolutionFourthDerivative ν (line x (T ω) (a*r)) j k l m*T ω l*T ω m))
    hi (fun j k => s.integrable_secondFourthKernel ν μ T hT hbound x ha j k)]
  apply integral_congr_ae
  exact ae_of_all _ fun z => s.variable_fourthTensor_pair_integral ν x (T z.1) (T z.2) a

theorem variableFourthRowC_eq_freshPair
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Vector p) (hT : Measurable T) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (x : Vector p) (q d : ℝ) {a : ℝ} (ha : a ≠ 0) :
    s.variableFourthRowC ν μ T x q a d = s.variableFourthRowC_freshPair ν μ T x q a d := by
  have hi (j k l : Fin p) : Integrable (fun ω => T ω j*T ω k*T ω l) μ := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      integrable_bounded_coordinate_product μ T hT hbound (![j,k,l] : Fin 3 → Fin p)
  unfold variableFourthRowC variableFourthRowC_freshPair
  congr 1
  rw [Companion.integral_fresh_pair_tensor3 μ (fun ω j k l => T ω j*T ω k*T ω l)
    (fun ω j k l => ∫ r in (0 : ℝ)..1,
      (∑ m, s.convolutionFourthDerivative ν (line x (T ω) (a*r)) j k l m*T ω m))
    hi (fun j k l => s.integrable_thirdFourthKernel ν μ T hT x ha j k l)]
  apply integral_congr_ae
  exact ae_of_all _ fun z => s.variable_fourthTensor_triple_integral ν x (T z.1) (T z.2) a

private theorem variable_base_interval_to_product
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (W V U₁ U₂ U₃ U₄ : Ω × Ξ → Vector p)
    (hW : Measurable W) (hV : Measurable V)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hU₃ : Measurable U₃) (hU₄ : Measurable U₄)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb₁ : ∀ᵐ ω ∂μ.prod ρ, ‖U₁ ω‖ ≤ δ) (hb₂ : ∀ᵐ ω ∂μ.prod ρ, ‖U₂ ω‖ ≤ δ)
    (hb₃ : ∀ᵐ ω ∂μ.prod ρ, ‖U₃ ω‖ ≤ δ) (hb₄ : ∀ᵐ ω ∂μ.prod ρ, ‖U₄ ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    ((∫ ω, (∫ η, (∫ r in (0 : ℝ)..1, K r *
      s.convolutionFourthTensor ν (line (W (ω, η)) (V (ω, η)) (a * r))
        (U₁ (ω, η)) (U₂ (ω, η)) (U₃ (ω, η)) (U₄ (ω, η))) ∂ρ) ∂μ) =
      ∫ r in (0 : ℝ)..1, K r * (∫ z,
        s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
          (U₁ z) (U₂ z) (U₃ z) (U₄ z) ∂μ.prod ρ)) ∧
    IntervalIntegrable (fun r => K r * (∫ z,
      s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
        (U₁ z) (U₂ z) (U₃ z) (U₄ z) ∂μ.prod ρ)) volume 0 1 := by
  have hi := s.integrable_convolutionFourthTensor_interval_prod ν (μ.prod ρ) W V U₁ U₂ U₃ U₄
    hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK
  constructor
  · calc
      _ = ∫ z, (∫ r in (0 : ℝ)..1, K r *
          s.convolutionFourthTensor ν (line (W z) (V z) (a * r))
            (U₁ z) (U₂ z) (U₃ z) (U₄ z)) ∂μ.prod ρ := by
        simpa only [intervalIntegral.integral_of_le zero_le_one] using
          (integral_prod _ hi.integral_prod_left).symm
      _ = _ := s.integral_interval_convolutionFourthTensor_swap ν (μ.prod ρ) W V U₁ U₂ U₃ U₄
        hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK
  · exact s.intervalIntegrable_integral_convolutionFourthTensor ν (μ.prod ρ) W V U₁ U₂ U₃ U₄
      hW hV hU₁ hU₂ hU₃ hU₄ hδ hb₁ hb₂ hb₃ hb₄ a K hK

private theorem variable_interval_weighted_sum2 {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ → ℝ) (c : α → β → ℝ) (K : ℝ → ℝ)
    (hi : ∀ i j, IntervalIntegrable (fun r => K r * f i j r) volume 0 1) :
    (∑ i, ∑ j, c i j * (∫ r in (0 : ℝ)..1, K r * f i j r)) =
      ∫ r in (0 : ℝ)..1, K r * ∑ i, ∑ j, c i j * f i j r := by
  classical
  have hinner (i : α) : (∑ j, c i j * (∫ r in (0 : ℝ)..1, K r * f i j r)) =
      ∫ r in (0 : ℝ)..1, ∑ j, c i j * (K r * f i j r) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => (hi i j).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  have ho := intervalIntegral.integral_finset_sum (s := Finset.univ) (fun i _ =>
    IntervalIntegrable.sum Finset.univ (fun j _ => (hi i j).const_mul (c i j)))
  simp only [Finset.sum_apply] at ho
  rw [← ho]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


def variableFourthPathIntegrandA {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a r : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ z : Ω × Ω, s.convolutionFourthTensor ν
      (line (x+a • maskObservationSum ξ (Function.update mask i false) z.1) (ξ i z.2) (a*r))
      (ξ i z.2) (ξ i z.2) (ξ i z.2) (ξ i z.2) ∂μ.prod μ

def variableFourthPathIntegrandB {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a r : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x+a • maskObservationSum ξ (Function.update mask i false) z.1) (ξ i z.2.2) (a*r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) (ξ i z.2.2) ∂μ.prod (μ.prod μ)

def variableFourthPathIntegrandC {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a r : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x+a • maskObservationSum ξ (Function.update mask i false) z.1) (ξ i z.2.2) (a*r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) ∂μ.prod (μ.prod μ)

def variableSelectorFourthA {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a c b : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ ω, s.variableFourthRowA ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ

def variableSelectorFourthB {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ ω, s.variableFourthRowB ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a ∂μ

def variableSelectorFourthC {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a d : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ ω, s.variableFourthRowC ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a d ∂μ

theorem variableSelectorFourthRemainder_eq_add
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) (q a c b d : ℝ)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    s.variableSelectorFourthRemainder ν μ ξ x q a c b d =
      s.variableSelectorFourthA ν μ ξ x q a c b+s.variableSelectorFourthB ν μ ξ x q a+
        s.variableSelectorFourthC ν μ ξ x q a d := by
  unfold variableSelectorFourthRemainder variableSelectorFourthA variableSelectorFourthB variableSelectorFourthC
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mask _
  have hi := s.integrable_variableFourthRows_base ν μ (ξ i)
    (fun ω => x+a • maskObservationSum ξ (Function.update mask i false) ω)
    (h.measurable i) (measurable_const.add (measurable_const.smul
      (measurable_maskObservationSum ξ h.measurable _))) h.delta_nonneg (h.bounded i) (h.centered i)
    q a c b d h2 h3
  rw [integral_add
    (f := fun ω => s.variableFourthRowA ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b+
      s.variableFourthRowB ν μ (ξ i) (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a)
    (g := fun ω => s.variableFourthRowC ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a d)
    (hi.1.add hi.2.1) hi.2.2,
    integral_add
    (f := fun ω => s.variableFourthRowA ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b)
    (g := fun ω => s.variableFourthRowB ν μ (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a) hi.1 hi.2.1]
  ring

theorem variableSelectorFourthA_eq_interval_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) (q a c b : ℝ) :
    s.variableSelectorFourthA ν μ ξ x q a c b =
      ∫ r in (0 : ℝ)..1, (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*
        s.variableFourthPathIntegrandA ν μ ξ x q a r := by
  let K : ℝ → ℝ := fun r => c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2
  let f := fun (i : Fin n) (mask : Kane.Cube n) (r : ℝ) =>
    ∫ z : Ω × Ω, s.convolutionFourthTensor ν
      (line (x+a • maskObservationSum ξ (Function.update mask i false) z.1) (ξ i z.2) (a*r))
        (ξ i z.2) (ξ i z.2) (ξ i z.2) (ξ i z.2) ∂μ.prod μ
  have hd (i : Fin n) (mask : Kane.Cube n) :
      (∫ ω, s.variableFourthRowA ν μ (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ) =
          (∫ r in (0 : ℝ)..1, K r*f i mask r) ∧
      IntervalIntegrable (fun r => K r*f i mask r) volume 0 1 := by
    have hbase : Measurable (fun z : Ω × Ω => x+a • maskObservationSum ξ (Function.update mask i false) z.1) :=
      (measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ h.measurable _))).comp measurable_fst
    have hrow : Measurable (fun z : Ω × Ω => ξ i z.2) := (h.measurable i).comp measurable_snd
    have hb : ∀ᵐ z ∂μ.prod μ, ‖ξ i z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae (h.bounded i)
    simpa only [variableFourthRowA, convolutionTranslationD4, convolutionFourthTensor] using
      s.variable_base_interval_to_product ν μ μ
        (fun z => x+a • maskObservationSum ξ (Function.update mask i false) z.1)
        (fun z => ξ i z.2) (fun z => ξ i z.2) (fun z => ξ i z.2) (fun z => ξ i z.2) (fun z => ξ i z.2)
        hbase hrow hrow hrow hrow hrow h.delta_nonneg hb hb hb hb a K (by dsimp [K]; fun_prop)
  unfold variableSelectorFourthA
  simp_rw [(hd _ _).1]
  exact variable_interval_weighted_sum2 f (fun _ mask => Kane.maskWeight q mask) K (fun i mask => (hd i mask).2)

theorem variableSelectorFourthB_eq_interval_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) (q : ℝ) {a : ℝ} (ha : a ≠ 0) :
    s.variableSelectorFourthB ν μ ξ x q a = q*a^2/2 *
      ∫ r in (0 : ℝ)..1, (1 - r) * s.variableFourthPathIntegrandB ν μ ξ x q a r := by
  let f := fun (i : Fin n) (mask : Kane.Cube n) (r : ℝ) =>
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x + a • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2.2) (a * r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) (ξ i z.2.2) ∂μ.prod (μ.prod μ)
  have hdata (i : Fin n) (mask : Kane.Cube n) :
      ((∫ ω, (∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1, (1 - r) *
        s.convolutionFourthTensor ν
          (line (x + a • maskObservationSum ξ (Function.update mask i false) ω)
            (ξ i z.2) (a * r))
          (ξ i z.1) (ξ i z.1) (ξ i z.2) (ξ i z.2)) ∂μ.prod μ) ∂μ) =
        ∫ r in (0 : ℝ)..1, (1 - r) * f i mask r) ∧
      IntervalIntegrable (fun r => (1 - r) * f i mask r) volume 0 1 := by
    have hbase : Measurable (fun z : Ω × (Ω × Ω) =>
        x + a • maskObservationSum ξ (Function.update mask i false) z.1) :=
      (measurable_const.add (measurable_const.smul
        (measurable_maskObservationSum ξ h.measurable _))).comp measurable_fst
    have hrow₁ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.1) :=
      (h.measurable i).comp (measurable_fst.comp measurable_snd)
    have hrow₂ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.2) :=
      (h.measurable i).comp (measurable_snd.comp measurable_snd)
    have hb₁ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.1‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_fst.ae (h.bounded i))
    have hb₂ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.2‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
    exact s.variable_base_interval_to_product ν μ (μ.prod μ)
      (fun z => x + a • maskObservationSum ξ (Function.update mask i false) z.1)
      (fun z => ξ i z.2.2) (fun z => ξ i z.2.1) (fun z => ξ i z.2.1)
      (fun z => ξ i z.2.2) (fun z => ξ i z.2.2)
      hbase hrow₂ hrow₁ hrow₁ hrow₂ hrow₂ h.delta_nonneg hb₁ hb₁ hb₂ hb₂
      a (fun r => 1 - r) (continuous_const.sub continuous_id)
  have heq (i : Fin n) (mask : Kane.Cube n) :
      (∫ ω, s.variableFourthRowB ν μ (ξ i)
        (x + a • maskObservationSum ξ (Function.update mask i false) ω) q a ∂μ) =
      q*a^2/2 * (∫ r in (0 : ℝ)..1, (1 - r) * f i mask r) := by
    simp_rw [s.variableFourthRowB_eq_freshPair ν μ (ξ i) (h.measurable i) (h.bounded i) _ q ha]
    unfold variableFourthRowB_freshPair
    rw [integral_const_mul]
    exact congrArg (fun y => q*a^2/2 * y) (hdata i mask).1
  unfold variableSelectorFourthB
  simp_rw [heq]
  calc
    _ = q*a^2/2 * (∑ i, ∑ mask,
        Kane.maskWeight q mask *
          (∫ r in (0 : ℝ)..1, (1 - r) * f i mask r)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := congrArg (fun y => q*a^2/2 * y)
      (variable_interval_weighted_sum2 f (fun _ mask => Kane.maskWeight q mask)
        (fun r => 1 - r) (fun i mask => (hdata i mask).2))


theorem variableSelectorFourthC_eq_interval_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (x : Vector p) (q d : ℝ) {a : ℝ} (ha : a ≠ 0) :
    s.variableSelectorFourthC ν μ ξ x q a d = -d*q*a *
      ∫ r in (0 : ℝ)..1, s.variableFourthPathIntegrandC ν μ ξ x q a r := by
  let f := fun (i : Fin n) (mask : Kane.Cube n) (r : ℝ) =>
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor ν
      (line (x + a • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2.2) (a * r))
      (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.1) (ξ i z.2.2) ∂μ.prod (μ.prod μ)
  have hdata (i : Fin n) (mask : Kane.Cube n) :
      ((∫ ω, (∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1,
        s.convolutionFourthTensor ν
          (line (x + a • maskObservationSum ξ (Function.update mask i false) ω)
            (ξ i z.2) (a * r))
          (ξ i z.1) (ξ i z.1) (ξ i z.1) (ξ i z.2)) ∂μ.prod μ) ∂μ) =
        ∫ r in (0 : ℝ)..1, f i mask r) ∧
      IntervalIntegrable (f i mask) volume 0 1 := by
    have hbase : Measurable (fun z : Ω × (Ω × Ω) =>
        x + a • maskObservationSum ξ (Function.update mask i false) z.1) :=
      (measurable_const.add (measurable_const.smul
        (measurable_maskObservationSum ξ h.measurable _))).comp measurable_fst
    have hrow₁ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.1) :=
      (h.measurable i).comp (measurable_fst.comp measurable_snd)
    have hrow₂ : Measurable (fun z : Ω × (Ω × Ω) => ξ i z.2.2) :=
      (h.measurable i).comp (measurable_snd.comp measurable_snd)
    have hb₁ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.1‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_fst.ae (h.bounded i))
    have hb₂ : ∀ᵐ z ∂μ.prod (μ.prod μ), ‖ξ i z.2.2‖ ≤ δ :=
      Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
    simpa only [one_mul] using s.variable_base_interval_to_product ν μ (μ.prod μ)
      (fun z => x + a • maskObservationSum ξ (Function.update mask i false) z.1)
      (fun z => ξ i z.2.2) (fun z => ξ i z.2.1) (fun z => ξ i z.2.1)
      (fun z => ξ i z.2.1) (fun z => ξ i z.2.2)
      hbase hrow₂ hrow₁ hrow₁ hrow₁ hrow₂ h.delta_nonneg hb₁ hb₁ hb₁ hb₂
      a (fun _ => 1) continuous_const
  have heq (i : Fin n) (mask : Kane.Cube n) :
      (∫ ω, s.variableFourthRowC ν μ (ξ i)
        (x + a • maskObservationSum ξ (Function.update mask i false) ω) q a d ∂μ) =
      -d*q*a * (∫ r in (0 : ℝ)..1, f i mask r) := by
    simp_rw [s.variableFourthRowC_eq_freshPair ν μ (ξ i) (h.measurable i) (h.bounded i) _ q d ha]
    unfold variableFourthRowC_freshPair
    rw [integral_const_mul]
    exact congrArg (fun y => -d*q*a * y) (hdata i mask).1
  unfold variableSelectorFourthC
  simp_rw [heq]
  calc
    _ = -d*q*a * (∑ i, ∑ mask,
        Kane.maskWeight q mask *
          (∫ r in (0 : ℝ)..1, f i mask r)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := by
      apply congrArg (fun y => -d*q*a * y)
      simpa only [one_mul] using
        variable_interval_weighted_sum2 f (fun _ mask => Kane.maskWeight q mask)
          (fun _ => 1) (fun i mask => by simpa only [one_mul] using (hdata i mask).2)

end
end RectangleCLT.FaceSmoother

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem variable_same_copy_fourth_kernel (γ γ' : ℝ → ℝ) {t : ℝ}
    (hγ : γ t ≠ 0) (r : ℝ) :
    variableRetentionDerivative γ γ' t*(γ t)^4/6*(1-r)^3+
      (variableRetention γ t*γ' t)*(γ t)^3/2*(1-r)^2 =
        seededFourthKernel (γ t) (variableEta γ γ' t) r := by
  unfold variableRetentionDerivative variableRetention variableEta seededFourthKernel
  field_simp [hγ]
  <;> ring

theorem variable_pair_fourth_kernel (γ : ℝ → ℝ) {t : ℝ} (hγ : γ t ≠ 0) :
    variableRetention γ t*(γ t)^2/2 = (1-t)/2 := by
  rw [variable_covariance_calibration γ hγ]

end
end RectangleCLT.Companion.SplitV4

namespace RectangleCLT.FaceSmoother
noncomputable section
variable {p : ℕ} (s : FaceSmoother p)

theorem variableSelectorFourthRemainder_eq_manuscript
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (γ γ' : ℝ → ℝ) (x : Vector p) {t : ℝ} (hpos : 0 < γ t) :
    s.variableSelectorFourthRemainder ν μ ξ x
      (Companion.SplitV4.variableRetention γ t) (γ t)
      (Companion.SplitV4.variableRetentionDerivative γ γ' t)
      (Companion.SplitV4.variableRetention γ t*γ' t) ((-(γ t)+(1-t)*γ' t)/6) =
      (∫ r in (0 : ℝ)..1, Companion.SplitV4.seededFourthKernel (γ t)
        (Companion.SplitV4.variableEta γ γ' t) r * s.variableFourthPathIntegrandA ν μ ξ x
          (Companion.SplitV4.variableRetention γ t) (γ t) r) +
      (1-t)/2*(∫ r in (0 : ℝ)..1, (1-r)*s.variableFourthPathIntegrandB ν μ ξ x
        (Companion.SplitV4.variableRetention γ t) (γ t) r) +
      (1-t)/6*(1-Companion.SplitV4.variableEta γ γ' t)*
        (∫ r in (0 : ℝ)..1, s.variableFourthPathIntegrandC ν μ ξ x
          (Companion.SplitV4.variableRetention γ t) (γ t) r) := by
  have h2 : Companion.SplitV4.variableRetentionDerivative γ γ' t*(γ t)^2/2+
      (Companion.SplitV4.variableRetention γ t*γ' t)*γ t = -(1/2 : ℝ) := by
    unfold Companion.SplitV4.variableRetentionDerivative Companion.SplitV4.variableRetention
    field_simp [hpos.ne']
    <;> ring
  have h3 : Companion.SplitV4.variableRetentionDerivative γ γ' t*(γ t)^3/6+
      (Companion.SplitV4.variableRetention γ t*γ' t)*(γ t)^2/2 = (-(γ t)+(1-t)*γ' t)/6 := by
    unfold Companion.SplitV4.variableRetentionDerivative Companion.SplitV4.variableRetention
    field_simp [hpos.ne']
    <;> ring
  rw [s.variableSelectorFourthRemainder_eq_add ν μ ξ h x _ _ _ _ _ h2 h3,
    s.variableSelectorFourthA_eq_interval_integral ν μ ξ h x,
    s.variableSelectorFourthB_eq_interval_integral ν μ ξ h x _ hpos.ne',
    s.variableSelectorFourthC_eq_interval_integral ν μ ξ h x _ _ hpos.ne']
  simp_rw [Companion.SplitV4.variable_same_copy_fourth_kernel γ γ' hpos.ne',
    Companion.SplitV4.variable_pair_fourth_kernel γ hpos.ne',
    Companion.SplitV4.variable_independent_copy_cubic_coefficient γ γ' hpos.ne']

/-- Exact manuscript kernels for the general-amplitude seeded identity,
under the actual independent finite-mask probability law. Each outer integral
is the proved product-law realization of the corresponding fourth tensor.
This theorem specializes the test to the actual face smoother. -/
theorem hasDerivAt_integral_variableSeededInterpolationLaw_manuscript
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < γ r)
    (hq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Companion.SplitV4.variableRetention γ r ∈ Set.Icc (0 : ℝ) 1)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hcont : ContinuousAt γ' t) :
    HasDerivAt (fun r => ∫ y, s.F (x+y)
      ∂Companion.SplitV4.variableSeededInterpolationLaw μ ξ A γ ε r)
      (((-(γ t)+(1-t)*γ' t)/6)*s.variableSignedCubicPathTerm
          (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x (Companion.SplitV4.variableRetention γ t) (γ t) +
       ((∫ r in (0 : ℝ)..1, Companion.SplitV4.seededFourthKernel (γ t)
          (Companion.SplitV4.variableEta γ γ' t) r * s.variableFourthPathIntegrandA
            (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x (Companion.SplitV4.variableRetention γ t) (γ t) r) +
        (1-t)/2*(∫ r in (0 : ℝ)..1, (1-r)*s.variableFourthPathIntegrandB
          (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x (Companion.SplitV4.variableRetention γ t) (γ t) r) +
        (1-t)/6*(1-Companion.SplitV4.variableEta γ γ' t)*
          (∫ r in (0 : ℝ)..1, s.variableFourthPathIntegrandC
            (gaussianLaw (Real.sqrt (t+ε) • A)) μ ξ x (Companion.SplitV4.variableRetention γ t) (γ t) r))) t := by
  rw [← s.variableSelectorFourthRemainder_eq_manuscript _ μ ξ h γ γ' x (hpos t ⟨ht, ht1⟩)]
  exact s.hasDerivAt_integral_variableSeededInterpolationLaw_fourth_identity
    μ ξ h A hA γ γ' hε hderiv hpos hq x ht ht1 hcont

end
end RectangleCLT.FaceSmoother

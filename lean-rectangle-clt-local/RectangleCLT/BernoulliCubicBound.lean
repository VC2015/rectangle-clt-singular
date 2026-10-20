import RectangleCLT.BernoulliComparisonFinal
import RectangleCLT.IndependentCovariance

/-! The actual common-point signed cubic contraction is controlled by the
maximum entry of the aggregate third-moment tensor. No absolute values are
introduced before the observations' third moments have been summed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

noncomputable def selectorThirdAbsoluteAverage
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  ∑ mask, Kane.maskWeight q mask *
    ∫ ω, ∑ j, ∑ k, ∑ l,
      |s.convolutionThirdDerivative ν (x + a • maskObservationSum ξ mask ω) j k l| ∂μ

omit [IsProbabilityMeasure ν] in
theorem selectorThirdAbsoluteAverage_nonneg
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (a : ℝ) :
    0 ≤ s.selectorThirdAbsoluteAverage ν μ ξ x q a := by
  apply Finset.sum_nonneg
  intro mask _
  apply mul_nonneg (Kane.maskWeight_nonneg hq hq1 mask)
  apply integral_nonneg
  intro ω
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => abs_nonneg _

theorem integrable_convolutionThirdDerivative_mask
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (x : Vector p) (a : ℝ)
    (mask : Kane.Cube n) (j k l : Fin p) :
    Integrable (fun ω => s.convolutionThirdDerivative ν
      (x + a • maskObservationSum ξ mask ω) j k l) μ :=
  integrable_bounded_test_comp μ _
    (measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ hξ mask))) _
    (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
    (fun y => s.norm_convolutionThirdDerivative_le ν y j k l)

/-- The finite absolute tensor sum may be interchanged with its genuine
observation integral and finite selector average. -/
theorem selectorThirdAbsoluteAverage_eq_sum
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (x : Vector p) (q a : ℝ) :
    s.selectorThirdAbsoluteAverage ν μ ξ x q a =
      ∑ j, ∑ k, ∑ l, ∑ mask, Kane.maskWeight q mask *
        ∫ ω, |s.convolutionThirdDerivative ν (x + a • maskObservationSum ξ mask ω) j k l| ∂μ := by
  have hi (mask : Kane.Cube n) (j k l : Fin p) :=
    (s.integrable_convolutionThirdDerivative_mask ν μ ξ hξ x a mask j k l).abs
  unfold selectorThirdAbsoluteAverage
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => hi _ j k l))),
    integral_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ => hi _ _ k l)),
    integral_finset_sum Finset.univ (fun l _ => hi _ _ _ l)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

omit [IsProbabilityMeasure ν] in
theorem abs_selectorThirdDerivativeAverage_le
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (x : Vector p) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (a : ℝ) (j k l : Fin p) :
    |s.selectorThirdDerivativeAverage ν μ ξ x q a j k l| ≤
      ∑ mask, Kane.maskWeight q mask *
        ∫ ω, |s.convolutionThirdDerivative ν (x + a • maskObservationSum ξ mask ω) j k l| ∂μ := by
  unfold selectorThirdDerivativeAverage
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro mask _
  rw [abs_mul, abs_of_nonneg (Kane.maskWeight_nonneg hq hq1 mask)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (Kane.maskWeight_nonneg hq hq1 mask)

/-- The aggregate signed third-moment tensor contracts against the actual
common-point third derivative with coefficient `gamma3`. Only measurability
is needed here: the convolution derivatives are globally bounded. -/
theorem abs_aggregate_third_contraction_le
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (x : Vector p)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (a : ℝ) :
    |∑ j, ∑ k, ∑ l, (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
      s.selectorThirdDerivativeAverage ν μ ξ x q a j k l| ≤
      gamma3 μ ξ * s.selectorThirdAbsoluteAverage ν μ ξ x q a := by
  have hentry (j k l : Fin p) :
      |∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ| ≤ gamma3 μ ξ := by
    apply (Finset.le_fold_max _).mpr
    exact Or.inr ⟨(j, k, l), Finset.mem_univ _, le_rfl⟩
  rw [s.selectorThirdAbsoluteAverage_eq_sum ν μ ξ hξ x q a]
  simp only [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  simpa only [Finset.mul_sum] using
    (mul_le_mul_of_nonneg_right (hentry j k l) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left
        (s.abs_selectorThirdDerivativeAverage_le ν μ ξ x hq hq1 a j k l) (gamma3_nonneg μ ξ))

/-- When the Gaussian covariance matches the bounded independent sum, the
actual path derivative contains only the aggregate cubic term and the
concrete corrected residual. -/
theorem abs_selectorHeatDerivative_le_cubic_add_residual
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      t / 3 * gamma3 μ ξ *
        s.selectorThirdAbsoluteAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
          (thinningProbability t) (thinningScale t) +
        |s.selectorCorrectedResidual (gaussianLaw (Real.sqrt t • A)) μ ξ x t| := by
  let ν := gaussianLaw (Real.sqrt t • A)
  have hzero (j k : Fin p) :
      (A * A.transpose) j k - (∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ) = 0 := by
    rw [hA, h.covariance_sum j k, sub_self]
  rw [s.selectorHeatDerivative_eq_commonPoint μ ξ h.measurable h.independent
    h.delta_nonneg h.bounded A x ht]
  simp_rw [hzero, zero_mul, Finset.sum_const_zero, mul_zero, zero_sub]
  have hc := s.abs_aggregate_third_contraction_le ν μ ξ h.measurable x
    (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) (thinningScale t)
  calc
    _ ≤ |-(t / 3 * (∑ j, ∑ k, ∑ l,
        (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
          s.selectorThirdDerivativeAverage ν μ ξ x (thinningProbability t) (thinningScale t) j k l))| +
        |s.selectorCorrectedResidual ν μ ξ x t| := abs_add _ _
    _ = t / 3 * |∑ j, ∑ k, ∑ l,
        (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
          s.selectorThirdDerivativeAverage ν μ ξ x (thinningProbability t) (thinningScale t) j k l| +
        |s.selectorCorrectedResidual ν μ ξ x t| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (div_nonneg ht (by norm_num))]
    _ ≤ t / 3 * (gamma3 μ ξ *
        s.selectorThirdAbsoluteAverage ν μ ξ x (thinningProbability t) (thinningScale t)) +
        |s.selectorCorrectedResidual ν μ ξ x t| :=
      add_le_add_right (mul_le_mul_of_nonneg_left hc (div_nonneg ht (by norm_num))) _
    _ = _ := by ring

end RectangleCLT.FaceSmoother

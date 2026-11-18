import RectangleCLTArxivV1.GaussianWidthOrder
import RectangleCLTCompanion.SplitV4.ConditionalTruncationBounds
import Mathlib.Probability.Variance

/-!
# Actual covariance and width transport for polynomial truncation

The conditional good laws are the archive's normalized restrictions of
actual marginal distributions. The bounds below use their computed
covariances and the proved Gaussian comparison theorem, including singular
covariances. They do not assume a truncation comparison estimate.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
  RectangleCLT.Companion.SplitV4
open scoped BigOperators

private theorem projection_sq_expand {p : ℕ} (v x : Vector p) :
    (dotProduct v x) ^ 2 = ∑ j, ∑ k, v j * (x j * x k) * v k := by
  calc
    _ = (∑ j, v j * x j) * (∑ k, v k * x k) := by rw [pow_two]; rfl
    _ = ∑ k, ∑ j, (v j * x j) * (v k * x k) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ j, ∑ k, (v j * x j) * (v k * x k) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))

/-- Finite-dimensional second moments commute with every real projection. -/
theorem integral_projection_sq {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (X : Ω → Vector p)
    (hpair : ∀ j k, Integrable (fun ω => X ω j * X ω k) μ) (v : Vector p) :
    (∫ ω, (dotProduct v (X ω)) ^ 2 ∂μ) =
      matrixQuadratic (fun j k => ∫ ω, X ω j * X ω k ∂μ) v := by
  simp_rw [projection_sq_expand]
  have hi (j k : Fin p) := ((hpair j k).const_mul (v j)).mul_const (v k)
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => hi j k))]
  unfold matrixQuadratic
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => hi j k)]
  simp only [integral_mul_const, integral_const_mul]

/-- Quadratic covariance is the actual variance of a real projection. -/
theorem matrixQuadratic_covariance_eq_variance {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Vector p) (hX : Measurable X)
    (hcoord : ∀ j, Integrable (fun ω => X ω j) μ)
    (hpair : ∀ j k, Integrable (fun ω => X ω j * X ω k) μ) (v : Vector p) :
    matrixQuadratic (covariance μ X) v = variance (fun ω => dotProduct v (X ω)) μ := by
  have hsq : Integrable (fun ω => (dotProduct v (X ω)) ^ 2) μ := by
    simp_rw [projection_sq_expand]
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        ((hpair j k).const_mul (v j)).mul_const (v k)))
  have hm : Measurable (fun ω => dotProduct v (X ω)) :=
    Finset.measurable_sum _ (fun j _ => measurable_const.mul ((measurable_pi_apply j).comp hX))
  have hmean : (∫ ω, dotProduct v (X ω) ∂μ) =
      dotProduct v (fun j => ∫ ω, X ω j ∂μ) := by
    rw [show (fun ω => dotProduct v (X ω)) = (fun ω => ∑ j, v j * X ω j) from rfl,
      integral_finset_sum Finset.univ (fun j _ => (hcoord j).const_mul _)]
    simp only [dotProduct, integral_const_mul]
  rw [variance_def' ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hsq)]
  change matrixQuadratic (covariance μ X) v =
    (∫ ω, (dotProduct v (X ω)) ^ 2 ∂μ) - (∫ ω, dotProduct v (X ω) ∂μ) ^ 2
  rw [integral_projection_sq μ X hpair v, hmean, projection_sq_expand]
  simp only [matrixQuadratic, covariance, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- A conditional good covariance is at most `4/3` of its original centered
covariance in every direction. The strict probability estimate is derived
from the envelope moment and `T ≥ 2B`. -/
theorem goodConditional_covariance_quadratic_le {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {B T q : ℝ}
    (h : ConditionalTruncationMomentHypotheses μ B T q) (v : Vector p) :
    matrixQuadratic (covariance (goodConditionalLaw μ T) id) v ≤
      (4 / 3 : ℝ) * matrixQuadratic (covariance μ id) v := by
  let P := μ.real (goodTruncationSet T)
  have hP : (3 / 4 : ℝ) ≤ P := by
    have hh := measureReal_add_measureReal_compl (μ := μ) (measurableSet_goodTruncationSet T)
    rw [measureReal_univ_eq_one] at hh
    dsimp [P]
    linarith [h.bad_probability_lt_quarter]
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hsq : Integrable (fun x : Vector p => (dotProduct v x) ^ 2) μ := by
    simp_rw [projection_sq_expand]
    exact integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        ((h.integrable_coordinate_pair j k).const_mul (v j)).mul_const (v k)))
  have hfull : matrixQuadratic (covariance μ id) v = ∫ x, (dotProduct v x) ^ 2 ∂μ := by
    have heq := integral_projection_sq μ id h.integrable_coordinate_pair v
    simp only [id_eq] at heq
    rw [heq]
    congr 1
    ext j k
    simp only [covariance, id_eq, h.centered, mul_zero, sub_zero]
  have hgood : matrixQuadratic (covariance (goodConditionalLaw μ T) id) v =
      P⁻¹ * (∫ x in goodTruncationSet T, (dotProduct v x) ^ 2 ∂μ) -
        (dotProduct v (conditionalGoodMean μ T)) ^ 2 := by
    have heq := integral_projection_sq (μ.restrict (goodTruncationSet T)) id
      (fun j k => (h.integrable_coordinate_pair j k).restrict) v
    simp only [id_eq] at heq
    rw [heq, projection_sq_expand]
    simp only [matrixQuadratic, goodConditional_covariance_restrict μ T h.good_mass_ne_zero,
      mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, P]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hgood, hfull]
  have hle := setIntegral_le_integral (s := goodTruncationSet T) hsq
    (ae_of_all μ (fun x => sq_nonneg (dotProduct v x)))
  have hinv : P⁻¹ ≤ (4 / 3 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hPpos).mpr
    linarith
  calc
    _ ≤ P⁻¹ * ∫ x in goodTruncationSet T, (dotProduct v x) ^ 2 ∂μ := sub_le_self _ (sq_nonneg _)
    _ ≤ P⁻¹ * ∫ x, (dotProduct v x) ^ 2 ∂μ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hPpos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hinv (integral_nonneg (fun x => sq_nonneg _))

/-- The Gaussian counterpart of the actual conditional law retains the
original width, up to the universal factor `sqrt(4/3)`. -/
theorem goodConditional_gaussianMaximumMean_le {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {B T q : ℝ}
    (h : ConditionalTruncationMomentHypotheses μ B T q)
    (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ id)
    (hC : C * C.transpose = covariance (goodConditionalLaw μ T) id) :
    gaussianMaximumMean C ≤ Real.sqrt (4 / 3 : ℝ) * gaussianMaximumMean A := by
  apply gaussianMaximumMean_le_sqrt_mul A C (4 / 3 : ℝ) (by norm_num)
  intro v
  rw [hA, hC]
  exact goodConditional_covariance_quadratic_le μ h v

/-- The covariance average commutes with its quadratic form. -/
theorem matrixQuadratic_average {p n : ℕ}
    (C : Fin n → Matrix (Fin p) (Fin p) ℝ) (a : ℝ) (v : Vector p) :
    matrixQuadratic (fun j k => a * ∑ i, C i j k) v =
      a * ∑ i, matrixQuadratic (C i) v := by
  simp only [matrixQuadratic, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ j, ∑ i, ∑ k, v j * (a * C i j k) * v k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, v j * (a * C i j k) * v k := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Conditional covariance is nonnegative in every direction, with its
value computed from the actual conditional integral. -/
theorem goodConditional_covariance_quadratic_nonneg {p : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] {T : ℝ}
    (hT : 0 ≤ T) (v : Vector p) :
    0 ≤ matrixQuadratic (covariance (goodConditionalLaw μ T) id) v := by
  rw [matrixQuadratic_covariance_eq_variance _ id measurable_id
    (integrable_goodConditional_coordinate μ hT)
    (integrable_goodConditional_coordinate_pair μ hT)]
  exact variance_nonneg _ _

/-- Every realized retained mask has covariance bounded by `4/3` of the
original averaged covariance. This is the printed conditional width order. -/
theorem conditionalCovarianceForMask_quadratic_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (mask : Fin n → Bool) (v : Vector p) :
    matrixQuadratic (conditionalCovarianceForMask μ T mask) v ≤
      (4 / 3 : ℝ) * matrixQuadratic (originalAverageCovariance μ) v := by
  have hleft : matrixQuadratic (conditionalCovarianceForMask μ T mask) v =
      (1 / (n : ℝ)) * ∑ i, matrixQuadratic
        (if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id) v := by
    unfold conditionalCovarianceForMask
    convert matrixQuadratic_average
      (fun i => if mask i then 0 else covariance (goodConditionalLaw (μ i) T) id)
      (1 / (n : ℝ)) v using 1
    congr 1
    funext j k
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split <;> rfl
  rw [hleft]
  unfold originalAverageCovariance
  rw [matrixQuadratic_average]
  rw [mul_left_comm (4 / 3 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : mask i = true
  · simp only [hi, if_true, matrixQuadratic, Matrix.zero_apply, mul_zero, zero_mul,
      Finset.sum_const_zero]
    have hn : 0 ≤ matrixQuadratic (covariance (μ i) id) v := by
      rw [matrixQuadratic_covariance_eq_variance _ id measurable_id
        (h i).integrable_coordinate (h i).integrable_coordinate_pair]
      exact variance_nonneg _ _
    positivity
  · simp only [hi, Bool.false_eq_true, if_false]
    exact goodConditional_covariance_quadratic_le (μ i) (h i) v

/-- Width control holds for every actual conditional Gaussian factor,
without exceptional-mask or covariance-rank assumptions. -/
theorem conditionalCovarianceForMask_gaussianMaximumMean_le {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (mask : Fin n → Bool) (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hC : C * C.transpose = conditionalCovarianceForMask μ T mask) :
    gaussianMaximumMean C ≤ Real.sqrt (4 / 3 : ℝ) * gaussianMaximumMean A := by
  apply gaussianMaximumMean_le_sqrt_mul A C (4 / 3 : ℝ) (by norm_num)
  intro v
  rw [hA, hC]
  exact conditionalCovarianceForMask_quadratic_le μ h mask v

/-- Dropping conditional summands decreases the actual covariance
quadratic form. The all-retained covariance is the printed matrix `Q₀`. -/
theorem conditionalCovarianceForMask_quadratic_le_allRetained {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {T : ℝ} (hT : 0 ≤ T) (mask : Fin n → Bool) (v : Vector p) :
    matrixQuadratic (conditionalCovarianceForMask μ T mask) v ≤
      matrixQuadratic (conditionalCovarianceForMask μ T (fun _ => false)) v := by
  have heq (b : Fin n → Bool) : matrixQuadratic (conditionalCovarianceForMask μ T b) v =
      (1 / (n : ℝ)) * ∑ i, matrixQuadratic
        (if b i then 0 else covariance (goodConditionalLaw (μ i) T) id) v := by
    unfold conditionalCovarianceForMask
    convert matrixQuadratic_average
      (fun i => if b i then 0 else covariance (goodConditionalLaw (μ i) T) id)
      (1 / (n : ℝ)) v using 1
    congr 1
    funext j k
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split <;> rfl
  rw [heq mask, heq (fun _ => false)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : mask i = true
  · simpa only [hi, if_true, Bool.false_eq_true, if_false, matrixQuadratic,
      Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] using
      goodConditional_covariance_quadratic_nonneg (μ i) hT v
  · simp only [hi, Bool.false_eq_true, if_false, le_refl]

end RectangleCLTArxivV1

import RectangleCLTCompanion.SupportCoordinates
import RectangleCLTCompanion.RestorationCoefficients
import Mathlib.MeasureTheory.Integral.Prod

/-!
The actual relative moment matrices in `eq:relative-moments` of split-V4.
The signed third moment is summed before its quadratic form is bounded.
The two fourth moment matrices are distinct: the second uses the product
of actual second moments, equivalently independent copies on a product law.
These definitions and envelope consequences do not prove the relative CLT.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

/-- Loewner comparison in real quadratic-form semantics. The moment
matrices below are symmetric, and no covariance inverse is used. -/
def QuadraticLE {p : ℕ} (A B : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∀ u : Vector p, matrixQuadratic A u ≤ matrixQuadratic B u

/-- `T_j`: the signed sum of the cubic coefficient matrices. -/
def relativeThirdMatrix {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    Matrix (Fin p) (Fin p) ℝ :=
  restorationCoefficient μ ξ (fun i ω => ξ i ω j)

/-- `Q_j`: the coordinate and rank-one factor use the same summand copy. -/
def relativeFourthMatrix {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    Matrix (Fin p) (Fin p) ℝ :=
  restorationCoefficient μ ξ (fun i ω => ξ i ω j ^ 2)

/-- `Qtilde_j`: the coordinate and rank-one factor use independent copies,
so the matrix entries are products of genuine second moments. -/
def relativeFreshFourthMatrix {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun k l => ∑ i, (∫ ω, ξ i ω j ^ 2 ∂μ) * (∫ ω, ξ i ω k * ξ i ω l ∂μ)

/-- Genuine entrywise moments accompany all quadratic-form comparisons.
The covariance is the actual covariance of the actual sum. Independent,
centered bounded data are supplied separately by the CLT setup. -/
structure RelativeMomentBounds {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (s₃ s₄ : ℝ) : Prop where
  measurable : ∀ i, Measurable (ξ i)
  second_integrable : ∀ i j k, Integrable (fun ω => ξ i ω j * ξ i ω k) μ
  third_integrable : ∀ i j k l,
    Integrable (fun ω => ξ i ω j * (ξ i ω k * ξ i ω l)) μ
  fourth_integrable : ∀ i j k l,
    Integrable (fun ω => ξ i ω j ^ 2 * (ξ i ω k * ξ i ω l)) μ
  s₃_nonneg : 0 ≤ s₃
  s₄_nonneg : 0 ≤ s₄
  third_lower : ∀ j, QuadraticLE ((-s₃) • covariance μ (sumVector ξ))
    (relativeThirdMatrix μ ξ j)
  third_upper : ∀ j, QuadraticLE (relativeThirdMatrix μ ξ j)
    (s₃ • covariance μ (sumVector ξ))
  fourth_upper : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))
  fresh_fourth_upper : ∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j)
    (s₄ • covariance μ (sumVector ξ))

private theorem quadratic_smul {p : ℕ} (a : ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (u : Vector p) :
    matrixQuadratic (a • A) u = a * matrixQuadratic A u := by
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Finite summation and Bochner integration commute for genuinely
integrable weighted entries; no pointwise version of an a.e. bound is needed. -/
theorem matrixQuadratic_restorationCoefficient_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (c : Fin n → Ω → ℝ)
    (hint : ∀ i j k, Integrable (fun ω => c i ω * (ξ i ω j * ξ i ω k)) μ)
    (u : Vector p) :
    matrixQuadratic (restorationCoefficient μ ξ c) u =
      ∑ i, ∫ ω, c i ω * (dotProduct u (ξ i ω)) ^ 2 ∂μ := by
  have hp (i : Fin n) (ω : Ω) :
      matrixQuadratic (fun j k => c i ω * (ξ i ω j * ξ i ω k)) u =
        c i ω * (dotProduct u (ξ i ω)) ^ 2 := by
    rw [show (dotProduct u (ξ i ω)) ^ 2 = matrixQuadratic (rankOne (ξ i ω)) u by
      exact (matrixQuadratic_rankOne_eq_square (ξ i ω) u).symm]
    simp only [matrixQuadratic, rankOne, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = ∑ i, matrixQuadratic
        (fun j k => ∫ ω, c i ω * (ξ i ω j * ξ i ω k) ∂μ) u := by
      unfold matrixQuadratic restorationCoefficient
      simp only [Finset.mul_sum, Finset.sum_mul]
      calc
        _ = ∑ j, ∑ i, ∑ k,
            (u j * ∫ ω, c i ω * (ξ i ω j * ξ i ω k) ∂μ) * u k := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [matrixQuadratic_integral μ _ (hint i) u]
      simp_rw [hp]

theorem relativeThirdMatrix_symmetric
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    (relativeThirdMatrix μ ξ j).transpose = relativeThirdMatrix μ ξ j :=
  restorationCoefficient_symmetric μ ξ _

theorem relativeFourthMatrix_symmetric
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    (relativeFourthMatrix μ ξ j).transpose = relativeFourthMatrix μ ξ j :=
  restorationCoefficient_symmetric μ ξ _

theorem relativeFreshFourthMatrix_symmetric
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    (relativeFreshFourthMatrix μ ξ j).transpose = relativeFreshFourthMatrix μ ξ j := by
  ext k l
  simp only [Matrix.transpose_apply, relativeFreshFourthMatrix]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)

/-- The product-law representation of `Qtilde_j` is an exact identity.
Integrability of this product integrand is proved below for the bounded data. -/
theorem relativeFreshFourthMatrix_eq_independent_copy
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    relativeFreshFourthMatrix μ ξ j =
      restorationCoefficient (μ.prod μ) (fun i z => ξ i z.2)
        (fun i z => ξ i z.1 j ^ 2) := by
  ext k l
  simp only [relativeFreshFourthMatrix, restorationCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_prod_mul (fun ω => ξ i ω j ^ 2)
    (fun ω => ξ i ω k * ξ i ω l)).symm

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

theorem integrable_relativeThird_entry (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (j k l : Fin p) :
    Integrable (fun ω => ξ i ω j * (ξ i ω k * ξ i ω l)) μ := by
  apply (h.integrable_coordinate_pair i k l).bdd_mul'
    (((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable)
  simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j

theorem ae_coordinate_sq_le (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (j : Fin p) : ∀ᵐ ω ∂μ, ξ i ω j ^ 2 ≤ δ ^ 2 := by
  filter_upwards [h.abs_coordinate_le i j] with ω hω
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) h.delta_nonneg).mpr hω

theorem integrable_relativeFourth_entry (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (j k l : Fin p) :
    Integrable (fun ω => ξ i ω j ^ 2 * (ξ i ω k * ξ i ω l)) μ := by
  apply (h.integrable_coordinate_pair i k l).bdd_mul'
    ((((measurable_pi_apply j).comp (h.measurable i)).pow_const 2).aestronglyMeasurable)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using ae_coordinate_sq_le h i j

theorem integrable_relativeFreshFourth_entry
    (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) (j k l : Fin p) :
    Integrable (fun z : Ω × Ω => ξ i z.1 j ^ 2 * (ξ i z.2 k * ξ i z.2 l))
      (μ.prod μ) := by
  have hi : Integrable (fun ω => ξ i ω j ^ 2) μ := by
    simpa only [pow_two] using h.integrable_coordinate_pair i j j
  exact hi.mul_prod (h.integrable_coordinate_pair i k l)

theorem relativeThirdMatrix_quadratic (h : BoundedIndependentHypotheses μ ξ δ)
    (j : Fin p) (u : Vector p) :
    matrixQuadratic (relativeThirdMatrix μ ξ j) u =
      ∑ i, ∫ ω, ξ i ω j * (dotProduct u (ξ i ω)) ^ 2 ∂μ :=
  matrixQuadratic_restorationCoefficient_of_integrable μ ξ _
    (fun i k l => integrable_relativeThird_entry h i j k l) u

theorem relativeFourthMatrix_quadratic (h : BoundedIndependentHypotheses μ ξ δ)
    (j : Fin p) (u : Vector p) :
    matrixQuadratic (relativeFourthMatrix μ ξ j) u =
      ∑ i, ∫ ω, ξ i ω j ^ 2 * (dotProduct u (ξ i ω)) ^ 2 ∂μ :=
  matrixQuadratic_restorationCoefficient_of_integrable μ ξ _
    (fun i k l => integrable_relativeFourth_entry h i j k l) u

theorem relativeFreshFourthMatrix_quadratic (h : BoundedIndependentHypotheses μ ξ δ)
    (j : Fin p) (u : Vector p) :
    matrixQuadratic (relativeFreshFourthMatrix μ ξ j) u =
      ∑ i, (∫ ω, ξ i ω j ^ 2 ∂μ) *
        (∫ ω, (dotProduct u (ξ i ω)) ^ 2 ∂μ) := by
  have hm : relativeFreshFourthMatrix μ ξ j =
      restorationCoefficient μ ξ (fun i _ => ∫ ω, ξ i ω j ^ 2 ∂μ) := by
    ext k l
    simp only [relativeFreshFourthMatrix, restorationCoefficient, integral_const_mul]
  rw [hm, matrixQuadratic_restorationCoefficient_of_integrable μ ξ _
    (fun i k l => (h.integrable_coordinate_pair i k l).const_mul _) u]
  simp only [integral_const_mul]

/-- The envelope controls the quadratic form of the signed aggregated
third matrix. The matrix definition retains all cancellation. -/
theorem envelope_relativeThirdMatrix_abs (h : BoundedIndependentHypotheses μ ξ δ)
    (j : Fin p) (u : Vector p) :
    |matrixQuadratic (relativeThirdMatrix μ ξ j) u| ≤
      δ * matrixQuadratic (covariance μ (sumVector ξ)) u := by
  rw [relativeThirdMatrix_quadratic h]
  calc
    _ ≤ ∑ i, |∫ ω, ξ i ω j * (dotProduct u (ξ i ω)) ^ 2 ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, δ * ∫ ω, (dotProduct u (ξ i ω)) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      have hp := integrable_observation_projection_sq h i u
      have hi : Integrable (fun ω => ξ i ω j * (dotProduct u (ξ i ω)) ^ 2) μ := by
        apply hp.bdd_mul' (((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable)
        simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j
      calc
        _ ≤ ∫ ω, |ξ i ω j * (dotProduct u (ξ i ω)) ^ 2| ∂μ :=
          abs_integral_le_integral_abs
        _ ≤ ∫ ω, δ * (dotProduct u (ξ i ω)) ^ 2 ∂μ := by
          apply integral_mono_ae hi.abs (hp.const_mul δ)
          filter_upwards [h.abs_coordinate_le i j] with ω hω
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_right hω (sq_nonneg _)
        _ = _ := integral_const_mul _ _
    _ = δ * (∑ i, ∫ ω, (dotProduct u (ξ i ω)) ^ 2 ∂μ) := (Finset.mul_sum ..).symm
    _ = _ := by rw [sum_integral_observation_projection_sq h]

theorem envelope_relativeFourthMatrix_le (h : BoundedIndependentHypotheses μ ξ δ)
    (j : Fin p) (u : Vector p) :
    matrixQuadratic (relativeFourthMatrix μ ξ j) u ≤
      δ ^ 2 * matrixQuadratic (covariance μ (sumVector ξ)) u := by
  rw [relativeFourthMatrix_quadratic h]
  calc
    _ ≤ ∑ i, δ ^ 2 * ∫ ω, (dotProduct u (ξ i ω)) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      have hp := integrable_observation_projection_sq h i u
      have hi : Integrable (fun ω => ξ i ω j ^ 2 * (dotProduct u (ξ i ω)) ^ 2) μ := by
        apply hp.bdd_mul'
          ((((measurable_pi_apply j).comp (h.measurable i)).pow_const 2).aestronglyMeasurable)
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using ae_coordinate_sq_le h i j
      rw [← integral_const_mul]
      apply integral_mono_ae hi (hp.const_mul (δ ^ 2))
      filter_upwards [ae_coordinate_sq_le h i j] with ω hω
      exact mul_le_mul_of_nonneg_right hω (sq_nonneg _)
    _ = δ ^ 2 * (∑ i, ∫ ω, (dotProduct u (ξ i ω)) ^ 2 ∂μ) := (Finset.mul_sum ..).symm
    _ = _ := by rw [sum_integral_observation_projection_sq h]

theorem envelope_relativeFreshFourthMatrix_le (h : BoundedIndependentHypotheses μ ξ δ)
    (j : Fin p) (u : Vector p) :
    matrixQuadratic (relativeFreshFourthMatrix μ ξ j) u ≤
      δ ^ 2 * matrixQuadratic (covariance μ (sumVector ξ)) u := by
  rw [relativeFreshFourthMatrix_quadratic h]
  calc
    _ ≤ ∑ i, δ ^ 2 * ∫ ω, (dotProduct u (ξ i ω)) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      have hi : Integrable (fun ω => ξ i ω j ^ 2) μ := by
        simpa only [pow_two] using h.integrable_coordinate_pair i j j
      have hb : (∫ ω, ξ i ω j ^ 2 ∂μ) ≤ δ ^ 2 := by
        calc
          _ ≤ ∫ _ : Ω, δ ^ 2 ∂μ :=
            integral_mono_ae hi (integrable_const _) (ae_coordinate_sq_le h i j)
          _ = _ := by simp
      exact mul_le_mul_of_nonneg_right hb (integral_nonneg (fun _ => sq_nonneg _))
    _ = δ ^ 2 * (∑ i, ∫ ω, (dotProduct u (ξ i ω)) ^ 2 ∂μ) := (Finset.mul_sum ..).symm
    _ = _ := by rw [sum_integral_observation_projection_sq h]

/-- Bounded independent centered summands always satisfy the exact
relative-moment contracts with s3=delta and s4=delta^2, for both fourth
matrices. Neither unit marginal variances nor nonsingular covariance is
needed for this prerequisite. -/
theorem relativeMomentBounds_of_envelope (h : BoundedIndependentHypotheses μ ξ δ) :
    RelativeMomentBounds μ ξ δ (δ ^ 2) where
  measurable := h.measurable
  second_integrable := h.integrable_coordinate_pair
  third_integrable := integrable_relativeThird_entry h
  fourth_integrable := integrable_relativeFourth_entry h
  s₃_nonneg := h.delta_nonneg
  s₄_nonneg := sq_nonneg _
  third_lower := by
    intro j u
    rw [quadratic_smul]
    have hh := (abs_le.mp (envelope_relativeThirdMatrix_abs h j u)).1
    nlinarith only [hh]
  third_upper := by
    intro j u
    rw [quadratic_smul]
    exact (abs_le.mp (envelope_relativeThirdMatrix_abs h j u)).2
  fourth_upper := by
    intro j u
    rw [quadratic_smul]
    exact envelope_relativeFourthMatrix_le h j u
  fresh_fourth_upper := by
    intro j u
    rw [quadratic_smul]
    exact envelope_relativeFreshFourthMatrix_le h j u

end

end RectangleCLT.Companion.SplitV4

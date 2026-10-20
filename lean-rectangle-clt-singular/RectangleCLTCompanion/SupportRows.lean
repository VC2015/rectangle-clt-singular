import RectangleCLTCompanion.SupportPseudoinverse

/-! Actual ambient support rows, reconstructed through a singular covariance
factor. Their summed second moments form a support projection bounded by the
identity, while every observable coordinate retains the original envelope. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

def whitenedObservation {Ω : Type*} {p q n : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (ω : Ω) : Vector q := (ambientWhitening A).mulVec (ξ i ω)

private theorem measurable_rectangular_mulVec {p q : ℕ}
    (L : Matrix (Fin q) (Fin p) ℝ) : Measurable L.mulVec := by
  apply measurable_pi_lambda
  intro j
  exact Finset.measurable_sum Finset.univ (fun k _ =>
    measurable_const.mul (measurable_pi_apply k))

private theorem dotProduct_mulVec_transpose {p q : ℕ}
    (L : Matrix (Fin q) (Fin p) ℝ) (v : Vector q) (x : Vector p) :
    dotProduct v (L.mulVec x) = dotProduct (L.transpose.mulVec v) x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

private theorem quadratic_eq_dotProduct {p : ℕ}
    (Q : Matrix (Fin p) (Fin p) ℝ) (v : Vector p) :
    matrixQuadratic Q v = dotProduct v (Q.mulVec v) := by
  simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Congruence of actual quadratic forms by a rectangular linear map. -/
theorem matrixQuadratic_congruence {p q : ℕ}
    (L : Matrix (Fin q) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ) (v : Vector q) :
    matrixQuadratic (L * Q * L.transpose) v = matrixQuadratic Q (L.transpose.mulVec v) := by
  rw [quadratic_eq_dotProduct, quadratic_eq_dotProduct]
  simp only [← Matrix.mulVec_mulVec]
  rw [dotProduct_mulVec_transpose]

/-- The support covariance is bounded by the ambient identity in its actual
quadratic-form order, with no factor-dependent multiplicative loss. -/
theorem ambientSupportProjection_quadratic_le {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (v : Vector q) :
    matrixQuadratic (ambientSupportProjection A) v ≤ vectorNormSq v := by
  have hh := matrixQuadratic_nonneg_of_posSemidef
    (one_sub_ambientSupportProjection_posSemidef A) v
  have heq : matrixQuadratic (1 - ambientSupportProjection A) v =
      vectorNormSq v - matrixQuadratic (ambientSupportProjection A) v := by
    simp only [matrixQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib,
      Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, vectorNormSq, pow_two]
  rw [heq] at hh
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {p q n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

omit [IsProbabilityMeasure μ] in
/-- Support-row selection is a fixed measurable linear map, not a choice
depending on the sample. -/
theorem whitenedObservation_measurable
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) : Measurable (whitenedObservation A ξ i) :=
  (measurable_rectangular_mulVec _).comp (h.measurable i)

omit [IsProbabilityMeasure μ] in
theorem whitenedObservation_independent
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ) : iIndepFun (whitenedObservation A ξ) μ :=
  h.independent.comp (fun _ => (ambientWhitening A).mulVec)
    (fun _ => measurable_rectangular_mulVec (ambientWhitening A))

theorem whitenedObservation_centered
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) (j : Fin q) :
    (∫ ω, whitenedObservation A ξ i ω j ∂μ) = 0 := by
  unfold whitenedObservation Matrix.mulVec dotProduct
  rw [integral_finset_sum Finset.univ (fun k _ =>
    (show Integrable (fun ω => ξ i ω k) μ from by
      simpa only [pow_one] using
        integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i k 1).const_mul _)]
  simp only [integral_const_mul, h.centered, mul_zero, Finset.sum_const_zero]

/-- Singular-factor reconstruction is valid on the actual observations,
using the already proved almost-sure covariance-support theorem. -/
theorem whitenedObservation_reconstruct
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) :
    (fun ω => A.mulVec (whitenedObservation A ξ i ω)) =ᵐ[μ] ξ i := by
  filter_upwards [observation_ae_mem_range_factor h A hA i] with ω hω
  exact factor_ambientWhitening_on_range A (ξ i ω) hω

/-- The observable maximum-norm envelope is preserved exactly. No uniform
bound is claimed on the norm of the pseudoinverse. -/
theorem whitenedObservation_projected_bounded
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) :
    ∀ᵐ ω ∂μ, ‖A.mulVec (whitenedObservation A ξ i ω)‖ ≤ δ := by
  filter_upwards [whitenedObservation_reconstruct h A hA i, h.bounded i] with ω hr hb
  simpa only [hr] using hb

/-- Exact ambient whitened covariance budget in every deterministic
direction. This equality precedes the dimension-free upper bound. -/
theorem sum_integral_whitened_projection_sq
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (v : Vector q) :
    (∑ i, ∫ ω, (dotProduct v (whitenedObservation A ξ i ω)) ^ 2 ∂μ) =
      matrixQuadratic (ambientSupportProjection A) v := by
  calc
    _ = matrixQuadratic (covariance μ (sumVector ξ)) ((ambientWhitening A).transpose.mulVec v) := by
      simp_rw [whitenedObservation, dotProduct_mulVec_transpose]
      exact sum_integral_observation_projection_sq h _
    _ = matrixQuadratic
        (ambientWhitening A * (A * A.transpose) * (ambientWhitening A).transpose) v := by
      rw [matrixQuadratic_congruence, hA]
    _ = _ := by rw [ambientWhitening_covariance]

/-- The support-row second-moment budget is at most identity, even when the
original covariance and factor are singular. -/
theorem whitenedObservation_covariance_budget
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (v : Vector q) :
    (∑ i, ∫ ω, (dotProduct v (whitenedObservation A ξ i ω)) ^ 2 ∂μ) ≤
      ∑ k, v k ^ 2 := by
  rw [sum_integral_whitened_projection_sq h A hA]
  exact ambientSupportProjection_quadratic_le A v

omit [IsProbabilityMeasure μ] in
/-- Unit marginal variances make every coordinate row of the factor a unit
Euclidean normal, without requiring linearly independent rows. -/
theorem factor_coordinate_normSq_eq_one
    (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (j : Fin p) :
    (∑ k, A j k ^ 2) = 1 := by
  have hh := congrFun (congrFun hA j) j
  have hs : (∑ k, A j k ^ 2) = covariance μ (sumVector ξ) j j := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hh
  exact hs.trans (hunit j)

/-- A finite auxiliary bound on the support coordinates. Its size is allowed
to depend on the factor; the observable envelope remains exactly `δ`. -/
def whiteningEnvelope (A : Matrix (Fin p) (Fin q) ℝ) (δ : ℝ) : ℝ :=
  δ * (1 + ∑ j, ∑ k, |ambientWhitening A j k|)

theorem whiteningEnvelope_nonneg (A : Matrix (Fin p) (Fin q) ℝ)
    (hδ : 0 ≤ δ) : 0 ≤ whiteningEnvelope A δ := by
  unfold whiteningEnvelope
  positivity

omit [IsProbabilityMeasure μ] in
theorem whitenedObservation_bounded
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) :
    ∀ᵐ ω ∂μ, ‖whitenedObservation A ξ i ω‖ ≤ whiteningEnvelope A δ := by
  filter_upwards [h.bounded i] with ω hω
  apply (pi_norm_le_iff_of_nonneg (whiteningEnvelope_nonneg A h.delta_nonneg)).2
  intro j
  change |∑ k, ambientWhitening A j k * ξ i ω k| ≤ _
  have hrow : (∑ k, |ambientWhitening A j k|) ≤
      ∑ j, ∑ k, |ambientWhitening A j k| :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin q => ∑ k : Fin p, |ambientWhitening A j k|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (Finset.mem_univ j)
  calc
    _ ≤ ∑ k, |ambientWhitening A j k * ξ i ω k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |ambientWhitening A j k| * δ := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((show |ξ i ω k| ≤ ‖ξ i ω‖ from by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (ξ i ω) k).trans hω)
        (abs_nonneg _)
    _ = (∑ k, |ambientWhitening A j k|) * δ := (Finset.sum_mul _ _ _).symm
    _ ≤ whiteningEnvelope A δ := by
      unfold whiteningEnvelope
      nlinarith [h.delta_nonneg]

/-- The actual support rows satisfy the standard bounded-independent data
structure. The auxiliary full-row bound is separate from the unchanged
original-coordinate bound in `whitenedObservation_projected_bounded`. -/
theorem whitenedObservation_hypotheses
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ) :
    BoundedIndependentHypotheses μ (whitenedObservation A ξ) (whiteningEnvelope A δ) where
  measurable := whitenedObservation_measurable h A
  independent := whitenedObservation_independent h A
  centered := whitenedObservation_centered h A
  bounded := whitenedObservation_bounded h A
  delta_nonneg := whiteningEnvelope_nonneg A h.delta_nonneg

private theorem matrix_eq_of_symmetric_quadratic_eq {q : ℕ}
    (M N : Matrix (Fin q) (Fin q) ℝ) (hM : M.transpose = M) (hN : N.transpose = N)
    (heq : ∀ v, matrixQuadratic M v = matrixQuadratic N v) : M = N := by
  have hdiag (j : Fin q) : M j j = N j j := by
    simpa only [localBasisVector_quadratic] using heq (localBasisVector j)
  ext j k
  have hpair := heq (twoCoordinateVector j k 1 1)
  simp only [matrixQuadratic_twoCoordinateVector, one_pow, one_mul, mul_one] at hpair
  have hMs : M k j = M j k := congrFun (congrFun hM j) k
  have hNs : N k j = N j k := congrFun (congrFun hN j) k
  linarith [hdiag j, hdiag k]

/-- The covariance of the actual transformed sum is the support projection,
not merely an upper bound imposed as an additional hypothesis. -/
theorem covariance_whitenedObservation
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    covariance μ (sumVector (whitenedObservation A ξ)) = ambientSupportProjection A := by
  apply matrix_eq_of_symmetric_quadratic_eq _ _ (covariance_transpose _ _)
    (ambientSupportProjection_transpose A)
  intro v
  rw [← sum_integral_observation_projection_sq (whitenedObservation_hypotheses h A) v]
  exact sum_integral_whitened_projection_sq h A hA v

end
end RectangleCLT.Companion

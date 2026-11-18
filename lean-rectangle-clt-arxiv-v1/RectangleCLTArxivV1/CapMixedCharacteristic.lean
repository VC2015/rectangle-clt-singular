import RectangleCLTArxivV1.BoundedCharacteristicFunction
import RectangleCLTArxivV1.SignedVariance

/-! Actual characteristic decay for a bounded independent array plus an
independent rectangular Gaussian image. The covariance quadratic form is
computed from the original observations before any small-box estimate. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open scoped BigOperators ComplexConjugate
noncomputable section

noncomputable def capMixedValue {Ω : Type*} {p r n : ℕ}
    (X : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin r) ℝ)
    (z : Ω × Vector r) : Vector p := sumVector X z.1 + A.mulVec z.2

noncomputable def capMixedCovariance {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin r) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := covariance μ (sumVector X) + A*A.transpose

theorem cap_matrixQuadratic_add {p : ℕ} (M N : Matrix (Fin p) (Fin p) ℝ) (w : Vector p) :
    matrixQuadratic (M+N) w = matrixQuadratic M w + matrixQuadratic N w := by
  simp only [matrixQuadratic,Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

theorem cap_dotProduct_sum {p n : ℕ} (w : Vector p) (x : Fin n → Vector p) :
    dotProduct w (∑ i, x i) = ∑ i, dotProduct w (x i) := by
  simp only [dotProduct,Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_comm

theorem cap_integral_projection_zero {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ X δ) (w : Vector p) (i : Fin n) :
    (∫ ω, dotProduct w (X i ω) ∂μ) = 0 := by
  have hi (j : Fin p) : Integrable (fun ω => X i ω j) μ := by
    simpa only [pow_one] using
      integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1
  change (∫ ω, ∑ j, w j*X i ω j ∂μ) = 0
  rw [integral_finset_sum Finset.univ (fun j _ => (hi j).const_mul (w j))]
  simp only [integral_const_mul,h.centered,mul_zero,Finset.sum_const_zero]

theorem norm_integral_unitPhase_sub_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (c : ℝ) :
    ‖∫ ω, unitPhase (F ω-c) ∂μ‖ = ‖∫ ω, unitPhase (F ω) ∂μ‖ := by
  simp_rw [unitPhase_sub]
  rw [integral_mul_const,norm_mul,Complex.norm_conj,norm_unitPhase,mul_one]

/-- All factors in this inequality are the actual characteristic functions
of the bounded array and independent Gaussian image. -/
theorem norm_integral_unitPhase_mixed_le
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (w : Vector p)
    (hhalf : ∀ i, ∀ᵐ ω ∂μ, |dotProduct w (X i ω)| ≤ 1/2) :
    ‖∫ z, unitPhase (dotProduct w (capMixedValue X A z))
      ∂μ.prod (standardGaussian r)‖ ≤
        Real.exp (-(2/Real.pi^2)*matrixQuadratic (capMixedCovariance μ X A) w) := by
  let f : Fin n → Ω → ℝ := fun i ω => dotProduct w (X i ω)
  have hproj : Measurable (fun x : Vector p => dotProduct w x) := by
    unfold dotProduct
    exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))
  have hm : ∀ i, Measurable (f i) := fun i => hproj.comp (h.measurable i)
  have hind : iIndepFun f μ := h.independent.comp (fun _ x => dotProduct w x) (fun _ => hproj)
  have hmean : ∀ i, (∫ ω, f i ω ∂μ) = 0 := cap_integral_projection_zero h w
  have hb := norm_integral_unitPhase_sum_le μ f hm hind hmean hhalf
  have hg := norm_integral_unitPhase_gaussian_linear_le A w
  have heq (z : Ω × Vector r) : unitPhase (dotProduct w (capMixedValue X A z)) =
      unitPhase (∑ i, f i z.1)*unitPhase (dotProduct w (A.mulVec z.2)) := by
    rw [capMixedValue,dotProduct_add]
    change unitPhase (dotProduct w (∑ i, X i z.1)+_) = _
    rw [cap_dotProduct_sum]
    unfold unitPhase f
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_add]
    ring
  simp_rw [heq]
  have hprod := integral_prod_mul (μ := μ) (ν := standardGaussian r)
    (fun ω => unitPhase (∑ i, f i ω)) (fun g => unitPhase (dotProduct w (A.mulVec g)))
  rw [hprod,norm_mul]
  apply (mul_le_mul hb hg (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  rw [show (∑ i, ∫ ω, f i ω^2 ∂μ) = matrixQuadratic (covariance μ (sumVector X)) w by
    exact sum_integral_observation_projection_sq h w,
    ← matrixQuadratic_gram A w]
  unfold capMixedCovariance
  rw [cap_matrixQuadratic_add]
  ring

end
end RectangleCLTArxivV1

import RectangleCLT.BernoulliPath
import RectangleCLT.GaussianMoments

/-!
# The actual probability law of the Bernoulli--Gaussian interpolation

The two components live on an independent product space. The bounded part
uses the proved Bernoulli selector mixture; the Gaussian factor is scaled
by `sqrt t`. Both endpoint laws are proved exactly. Differentiation and the
analytic comparison estimate remain separate obligations.
-/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

def arraySum {p n : ℕ} (a : Fin n → Vector p) : Vector p := ∑ i, a i

theorem measurable_arraySum (p n : ℕ) : Measurable (@arraySum p n) := by
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)

def interpolationSum {p n : ℕ} (x : (Fin n → Vector p) × Vector p) : Vector p :=
  arraySum x.1 + x.2

theorem measurable_interpolationSum (p n : ℕ) :
    Measurable (@interpolationSum p n) :=
  ((measurable_arraySum p n).comp measurable_fst).add measurable_snd

/-- A scaled Gaussian factor has covariance `t * (A Aᵀ)` for `t ≥ 0`.
The law is defined even when the covariance is singular. -/
def interpolatedGaussianFactor {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) : Matrix (Fin p) (Fin p) ℝ := Real.sqrt t • A

/-- A genuine probability law for the entire interpolation, with independent
bounded and Gaussian components supplied by the product construction. -/
def interpolationLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) : Measure (Vector p) :=
  ((bernoulliArrayLaw μ ξ t).prod (gaussianLaw (interpolatedGaussianFactor A t))).map
    interpolationSum

theorem interpolationLaw_isProbability {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (interpolationLaw μ ξ A t) := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  exact isProbabilityMeasure_map (measurable_interpolationSum p n).aemeasurable

@[simp] theorem gaussianLaw_zero (p : ℕ) :
    gaussianLaw (0 : Matrix (Fin p) (Fin p) ℝ) = Measure.dirac 0 := by
  have hzero : (0 : Matrix (Fin p) (Fin p) ℝ).mulVec =
      (fun _ : Vector p => (0 : Vector p)) := by
    funext x
    exact Matrix.zero_mulVec x
  rw [gaussianLaw, hzero, Measure.map_const, measure_univ, one_smul]

/-- The interpolated Gaussian covariance is linear in the path parameter. -/
theorem interpolatedGaussian_covariance {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    covariance (gaussianLaw (interpolatedGaussianFactor A t)) id =
      t • (A * A.transpose) := by
  rw [covariance_gaussianLaw]
  ext j k
  simp only [interpolatedGaussianFactor, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (Real.sqrt t) ^ 2 * (A j i * A k i) := by ring
    _ = _ := by rw [Real.sq_sqrt ht]

/-- The bounded endpoint is exactly the original observation-sum law. -/
theorem interpolationLaw_zero {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    interpolationLaw μ ξ A 0 = μ.map (sumVector ξ) := by
  unfold interpolationLaw
  rw [bernoulliArrayLaw_zero]
  simp only [interpolatedGaussianFactor, Real.sqrt_zero, zero_smul, gaussianLaw_zero]
  have hpair : Measurable (fun x : Fin n → Vector p => (x, (0 : Vector p))) :=
    measurable_id.prodMk measurable_const
  rw [Measure.prod_dirac, Measure.map_map (measurable_interpolationSum p n) hpair]
  have heq : interpolationSum ∘ (fun x : Fin n → Vector p => (x, (0 : Vector p))) =
      arraySum := by
    funext x
    simp [Function.comp_def, interpolationSum]
  rw [heq, Measure.map_map (measurable_arraySum p n) (measurable_pi_lambda _ hξ)]
  rfl

/-- The Gaussian endpoint contains no bounded summands. -/
theorem interpolationLaw_one {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    interpolationLaw μ ξ A 1 = gaussianLaw A := by
  unfold interpolationLaw
  rw [bernoulliArrayLaw_one]
  simp only [interpolatedGaussianFactor, Real.sqrt_one, one_smul]
  have hpair : Measurable (fun x : Vector p => ((0 : Fin n → Vector p), x)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.dirac_prod, Measure.map_map (measurable_interpolationSum p n) hpair]
  have heq : interpolationSum ∘ Prod.mk (0 : Fin n → Vector p) = id := by
    funext x
    simp [Function.comp_def, interpolationSum, arraySum]
  rw [heq, Measure.map_id]

end

end RectangleCLT

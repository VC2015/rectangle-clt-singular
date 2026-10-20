import RectangleCLT.IndependentCovariance
import RectangleCLT.BoundedCurvature
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual bounded independent observations have no mass outside their sum
covariance support. Projection second moments are computed before any support
coordinates are chosen, so no nondegeneracy or full inverse is required. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

private theorem dotProduct_sq_expand {p : ℕ} (v x : Fin p → ℝ) :
    (dotProduct v x) ^ 2 = ∑ j, ∑ k, v j * (x j * x k) * v k := by
  calc
    _ = (∑ j, v j * x j) * (∑ k, v k * x k) := by rw [pow_two]; rfl
    _ = ∑ k, ∑ j, (v j * x j) * (v k * x k) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ j, ∑ k, (v j * x j) * (v k * x k) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

theorem integrable_observation_projection_sq
    (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) (v : Vector p) :
    Integrable (fun ω => (dotProduct v (ξ i ω)) ^ 2) μ := by
  simp_rw [dotProduct_sq_expand]
  exact integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      ((h.integrable_coordinate_pair i j k).const_mul (v j)).mul_const (v k)))

theorem integral_observation_projection_sq
    (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) (v : Vector p) :
    (∫ ω, (dotProduct v (ξ i ω)) ^ 2 ∂μ) =
      ∑ j, ∑ k, v j * (∫ ω, ξ i ω j * ξ i ω k ∂μ) * v k := by
  simp_rw [dotProduct_sq_expand]
  have hi (j k : Fin p) := ((h.integrable_coordinate_pair i j k).const_mul (v j)).mul_const (v k)
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => hi j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => hi j k)]
  simp only [integral_mul_const, integral_const_mul]

/-- The actual summed second moments in any direction equal the quadratic
form of the actual sum covariance, including all singular directions. -/
theorem sum_integral_observation_projection_sq
    (h : BoundedIndependentHypotheses μ ξ δ) (v : Vector p) :
    (∑ i, ∫ ω, (dotProduct v (ξ i ω)) ^ 2 ∂μ) =
      matrixQuadratic (covariance μ (sumVector ξ)) v := by
  simp only [integral_observation_projection_sq h]
  unfold matrixQuadratic
  simp_rw [h.covariance_sum]
  calc
    _ = ∑ j, ∑ i, ∑ k, v j * (∫ ω, ξ i ω j * ξ i ω k ∂μ) * v k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, v j * (∫ ω, ξ i ω j * ξ i ω k ∂μ) * v k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

/-- A direction of zero total variance vanishes for every centered
independent observation almost surely. -/
theorem observation_projection_ae_zero_of_quadratic_zero
    (h : BoundedIndependentHypotheses μ ξ δ) (v : Vector p)
    (hv : matrixQuadratic (covariance μ (sumVector ξ)) v = 0) (i : Fin n) :
    (fun ω => dotProduct v (ξ i ω)) =ᵐ[μ] 0 := by
  have hs := sum_integral_observation_projection_sq h v
  rw [hv] at hs
  have hi0 : 0 ≤ ∫ ω, (dotProduct v (ξ i ω)) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hile : (∫ ω, (dotProduct v (ξ i ω)) ^ 2 ∂μ) ≤ 0 := by
    rw [← hs]
    exact Finset.single_le_sum (fun (k : Fin n) _ =>
      integral_nonneg (fun (ω : Ω) => sq_nonneg (dotProduct v (ξ k ω)))) (Finset.mem_univ i)
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (dotProduct v (ξ i ω)))
    (integrable_observation_projection_sq h i v)).mp (le_antisymm hile hi0)
  filter_upwards [hz] with ω hω
  exact sq_eq_zero_iff.mp hω

/-- The covariance factor's transpose kernel is the zero-variance support
annihilator. No inverse or lower eigenvalue bound enters this identity. -/
theorem matrixQuadratic_gram {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (v : Vector p) :
    matrixQuadratic (A * A.transpose) v = ∑ k, (A.transpose.mulVec v k) ^ 2 := by
  have hform : matrixQuadratic (A * A.transpose) v = dotProduct v ((A * A.transpose).mulVec v) := by
    simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [hform]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, pow_two]

/-- Every actual row annihilates every transpose-kernel direction. -/
theorem observation_projection_ae_zero_of_transpose_mulVec_zero
    (h : BoundedIndependentHypotheses μ ξ δ)
    {q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (v : Vector p) (hv : A.transpose.mulVec v = 0) (i : Fin n) :
    (fun ω => dotProduct v (ξ i ω)) =ᵐ[μ] 0 := by
  apply observation_projection_ae_zero_of_quadratic_zero h v _ i
  rw [← hA, matrixQuadratic_gram, hv]
  simp

/-- A linear functional on the finite product is its coordinate dot product. -/
theorem linearForm_eq_dotProduct {p : ℕ} (f : Vector p →ₗ[ℝ] ℝ) (x : Vector p) :
    f x = dotProduct (fun j => f (Pi.single j 1)) x := by
  classical
  have hx : x = ∑ j, x j • (Pi.single j 1 : Vector p) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

omit [IsProbabilityMeasure μ] in
/-- A finite quotient basis suffices to turn almost-sure annihilation of
linear functionals into almost-sure membership of a subspace. This avoids
an unjustified intersection over uncountably many null directions. -/
theorem ae_mem_submodule_of_linear_annihilators
    (X : Ω → Vector p) (S : Submodule ℝ (Vector p))
    (hX : ∀ f : Vector p →ₗ[ℝ] ℝ, (∀ x ∈ S, f x = 0) → (fun ω => f (X ω)) =ᵐ[μ] 0) :
    ∀ᵐ ω ∂μ, X ω ∈ S := by
  classical
  let b := Module.finBasis ℝ ((Vector p) ⧸ S)
  have hc (j : Fin (Module.finrank ℝ ((Vector p) ⧸ S))) :
      (fun ω => (b.coord j) (S.mkQ (X ω))) =ᵐ[μ] 0 := by
    apply hX ((b.coord j).comp S.mkQ)
    intro x hx
    have hz : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
    simp only [LinearMap.comp_apply, hz, map_zero]
  have hall := ae_all_iff.mpr hc
  filter_upwards [hall] with ω hω
  have hz : S.mkQ (X ω) = 0 := by
    apply b.ext_elem
    intro j
    simpa only [map_zero, Finsupp.zero_apply] using hω j
  exact (Submodule.Quotient.mk_eq_zero S).mp hz

/-- Every actual observation lies almost surely in the range of any factor
of its actual summed covariance. The factor may be rectangular or singular. -/
theorem observation_ae_mem_range_factor
    (h : BoundedIndependentHypotheses μ ξ δ)
    {q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) :
    ∀ᵐ ω ∂μ, ξ i ω ∈ LinearMap.range A.mulVecLin := by
  apply ae_mem_submodule_of_linear_annihilators (ξ i) (LinearMap.range A.mulVecLin)
  intro f hf
  let v : Vector p := fun j => f (Pi.single j 1)
  have hv : A.transpose.mulVec v = 0 := by
    funext k
    have ha := hf (A.mulVec (Pi.single k 1)) (LinearMap.mem_range.mpr ⟨Pi.single k 1, rfl⟩)
    have hcol : A.mulVec (Pi.single k 1) = fun j => A j k := by
      classical
      exact Matrix.mulVec_single_one A k
    rw [hcol, linearForm_eq_dotProduct] at ha
    simpa only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, v, mul_comm] using ha
  have hz := observation_projection_ae_zero_of_transpose_mulVec_zero h A hA v hv i
  filter_upwards [hz] with ω hω
  rw [linearForm_eq_dotProduct]
  exact hω

end
end RectangleCLT.Companion

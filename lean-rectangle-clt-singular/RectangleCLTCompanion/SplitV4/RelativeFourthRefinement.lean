import RectangleCLTCompanion.SplitV4.RelativeMoments

/-! The paper's fourth-only admissibility implies the signed third budget.
The third tensor is aggregated before taking an absolute value. Both fourth
matrices remain separate, including in singular covariance directions. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

private theorem cross_sq_le_of_quadratic_nonneg (A B C : ℝ) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ A*t^2 + 2*B*t + C) : B^2 ≤ A*C := by
  by_cases hz : A = 0
  · subst A
    by_cases hb : B = 0
    · simp [hb]
    · have hh := h (-(C+1)/(2*B))
      have heq : 0*(-(C+1)/(2*B))^2 + 2*B*(-(C+1)/(2*B)) + C = -1 := by
        field_simp
      rw [heq] at hh
      norm_num at hh
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    have hh := h (-B/A)
    have heq : A*(-B/A)^2 + 2*B*(-B/A) + C = (A*C-B^2)/A := by
      field_simp
      ring
    rw [heq] at hh
    have hn := (le_div_iff₀ hp).mp hh
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}

theorem relativeThirdMatrix_square_le_fourth_covariance
    (h : BoundedIndependentHypotheses μ ξ δ) (j : Fin p) (u : Vector p) :
    matrixQuadratic (relativeThirdMatrix μ ξ j) u ^ 2 ≤
      matrixQuadratic (relativeFourthMatrix μ ξ j) u *
        matrixQuadratic (covariance μ (sumVector ξ)) u := by
  have hA : 0 ≤ matrixQuadratic (relativeFourthMatrix μ ξ j) u := by
    rw [relativeFourthMatrix_quadratic h]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by positivity
  apply cross_sq_le_of_quadratic_nonneg _ _ _ hA
  intro t
  rw [relativeFourthMatrix_quadratic h, relativeThirdMatrix_quadratic h,
    ← sum_integral_observation_projection_sq h]
  have hterm (i : Fin n) : 0 ≤ t^2 * (∫ ω, ξ i ω j ^ 2 * (dotProduct u (ξ i ω))^2 ∂μ) +
      2*t * (∫ ω, ξ i ω j * (dotProduct u (ξ i ω))^2 ∂μ) +
      (∫ ω, (dotProduct u (ξ i ω))^2 ∂μ) := by
    have hiS := integrable_observation_projection_sq h i u
    have hiT := hiS.bdd_mul' (((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j)
    have hiA := hiS.bdd_mul' (c := δ^2)
      ((((measurable_pi_apply j).comp (h.measurable i)).pow_const 2).aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs, abs_sq] using ae_coordinate_sq_le h i j)
    have hpoint (ω : Ω) : 0 ≤ t^2 * (ξ i ω j ^ 2 * (dotProduct u (ξ i ω))^2) +
        (2*t) * (ξ i ω j * (dotProduct u (ξ i ω))^2) + (dotProduct u (ξ i ω))^2 := by
      nlinarith [sq_nonneg ((t*ξ i ω j+1)*dotProduct u (ξ i ω))]
    have hn : 0 ≤ ∫ ω, t^2 * (ξ i ω j ^ 2 * (dotProduct u (ξ i ω))^2) +
        (2*t) * (ξ i ω j * (dotProduct u (ξ i ω))^2) + (dotProduct u (ξ i ω))^2 ∂μ :=
      integral_nonneg hpoint
    have heq₁ := integral_add ((hiA.const_mul (t^2)).add (hiT.const_mul (2*t))) hiS
    have heq₂ := integral_add (hiA.const_mul (t^2)) (hiT.const_mul (2*t))
    dsimp only [Pi.add_apply, Function.comp_apply] at heq₁ heq₂
    rw [heq₁, heq₂, integral_const_mul, integral_const_mul] at hn
    exact hn
  have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hterm i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  nlinarith only [hh]

theorem relativeThirdMatrix_abs_le_sqrt_fourth
    (h : BoundedIndependentHypotheses μ ξ δ) {s₄ : ℝ} (hs₄ : 0 ≤ s₄)
    (hQ : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j)
      (s₄ • covariance μ (sumVector ξ))) (j : Fin p) (u : Vector p) :
    |matrixQuadratic (relativeThirdMatrix μ ξ j) u| ≤
      Real.sqrt s₄ * matrixQuadratic (covariance μ (sumVector ξ)) u := by
  have hS : 0 ≤ matrixQuadratic (covariance μ (sumVector ξ)) u := by
    rw [← sum_integral_observation_projection_sq h]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
  have hupper := hQ j u
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum] at hupper
  have hqu : matrixQuadratic (relativeFourthMatrix μ ξ j) u ≤
      s₄ * matrixQuadratic (covariance μ (sumVector ξ)) u := by
    convert hupper using 1 <;> unfold matrixQuadratic <;>
      simp only [Finset.mul_sum] <;> congr 1 <;> funext k <;> congr 1 <;> funext l <;> ring
  have hsq := (relativeThirdMatrix_square_le_fourth_covariance h j u).trans
    (mul_le_mul_of_nonneg_right hqu hS)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hS)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hs₄]
  nlinarith

theorem relativeMomentBounds_of_fourth_admissibility
    (h : BoundedIndependentHypotheses μ ξ δ) {s₄ : ℝ} (hs₄ : 0 ≤ s₄)
    (hQ : ∀ j, QuadraticLE (relativeFourthMatrix μ ξ j) (s₄ • covariance μ (sumVector ξ)))
    (hQfresh : ∀ j, QuadraticLE (relativeFreshFourthMatrix μ ξ j)
      (s₄ • covariance μ (sumVector ξ))) :
    RelativeMomentBounds μ ξ (Real.sqrt s₄) s₄ where
  measurable := h.measurable
  second_integrable := h.integrable_coordinate_pair
  third_integrable := integrable_relativeThird_entry h
  fourth_integrable := integrable_relativeFourth_entry h
  s₃_nonneg := Real.sqrt_nonneg _
  s₄_nonneg := hs₄
  third_lower := by
    intro j u
    have hh := (abs_le.mp (relativeThirdMatrix_abs_le_sqrt_fourth h hs₄ hQ j u)).1
    have heq : matrixQuadratic ((-Real.sqrt s₄) • covariance μ (sumVector ξ)) u =
        -Real.sqrt s₄ * matrixQuadratic (covariance μ (sumVector ξ)) u := by
      simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      congr 1; funext k; congr 1; funext l; ring
    rw [heq]
    linarith
  third_upper := by
    intro j u
    have hh := (abs_le.mp (relativeThirdMatrix_abs_le_sqrt_fourth h hs₄ hQ j u)).2
    have heq : matrixQuadratic ((Real.sqrt s₄) • covariance μ (sumVector ξ)) u =
        Real.sqrt s₄ * matrixQuadratic (covariance μ (sumVector ξ)) u := by
      simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      congr 1; funext k; congr 1; funext l; ring
    rw [heq]
    exact hh
  fourth_upper := hQ
  fresh_fourth_upper := hQfresh

end
end RectangleCLT.Companion.SplitV4

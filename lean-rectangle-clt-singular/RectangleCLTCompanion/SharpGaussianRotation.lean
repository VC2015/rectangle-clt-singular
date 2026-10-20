import RectangleCLTCompanion.SharpGaussianSplit
import RectangleCLTCompanion.SignedSurfaceGaussianSection

/-! The sum of two independent Gaussian halves has the original Gaussian
law, proved from actual orthogonal invariance of the product Gaussian. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion

noncomputable section

private def halfRotation (x : Vector 2) : Vector 2 :=
  ![(x 0 + x 1) / Real.sqrt 2, (x 0 - x 1) / Real.sqrt 2]

private theorem halfRotation_involutive (x : Vector 2) : halfRotation (halfRotation x) = x := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    simpa only [pow_two] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ext j
  fin_cases j <;> simp only [halfRotation, Matrix.cons_val_zero, Matrix.cons_val_one]
  · field_simp
  · field_simp

private theorem halfRotation_normSq (x : Vector 2) : vectorNormSq (halfRotation x) = vectorNormSq x := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [vectorNormSq, Fin.sum_univ_two, halfRotation, Matrix.cons_val_zero, Matrix.cons_val_one,
    div_pow, hs]
  ring

private def halfRotationLinear : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := (WithLp.equiv 2 (Vector 2)).symm (halfRotation ((WithLp.equiv 2 (Vector 2)) x))
  map_add' x y := by
    ext j
    fin_cases j
    · change ((x 0 + y 0) + (x 1 + y 1)) / Real.sqrt 2 =
        (x 0 + x 1) / Real.sqrt 2 + (y 0 + y 1) / Real.sqrt 2
      ring
    · change ((x 0 + y 0) - (x 1 + y 1)) / Real.sqrt 2 =
        (x 0 - x 1) / Real.sqrt 2 + (y 0 - y 1) / Real.sqrt 2
      ring
  map_smul' a x := by
    ext j
    fin_cases j
    · change (a * x 0 + a * x 1) / Real.sqrt 2 = a * ((x 0 + x 1) / Real.sqrt 2)
      ring
    · change (a * x 0 - a * x 1) / Real.sqrt 2 = a * ((x 0 - x 1) / Real.sqrt 2)
      ring

private theorem halfRotationLinear_involutive (x : EuclideanSpace ℝ (Fin 2)) :
    halfRotationLinear (halfRotationLinear x) = x := by
  change (WithLp.equiv 2 (Vector 2)).symm (halfRotation (halfRotation ((WithLp.equiv 2 (Vector 2)) x))) = x
  rw [halfRotation_involutive, Equiv.symm_apply_apply]

private def halfRotationIsometry : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := halfRotationLinear
      norm_map' := by
        intro x
        have hh := halfRotation_normSq ((WithLp.equiv 2 (Vector 2)) x)
        rw [SignedSurface.vectorNormSq_eq_euclidean_norm_sq,
          SignedSurface.vectorNormSq_eq_euclidean_norm_sq] at hh
        change ‖halfRotationLinear x‖ ^ 2 = ‖x‖ ^ 2 at hh
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh }
    (fun y => ⟨halfRotationLinear y, halfRotationLinear_involutive y⟩)

private theorem halfRotation_preserving :
    MeasurePreserving halfRotation (standardGaussian 2) (standardGaussian 2) := by
  have hh := SignedSurface.gaussianRotation_standardGaussian_preserving halfRotationIsometry
  convert hh using 1

private theorem scalar_half_sum_preserving :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + z.2) / Real.sqrt 2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (gaussianReal 0 1) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he : MeasurePreserving e (standardGaussian 2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    measurePreserving_piFinTwo (fun _ => gaussianReal 0 1)
  have hf : MeasurePreserving (Prod.fst : ℝ × ℝ → ℝ)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (gaussianReal 0 1) := by
    refine ⟨measurable_fst, ?_⟩
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hh := hf.comp (he.comp (halfRotation_preserving.comp (he.symm e)))
  convert hh using 1

/-- The actual normalized sum of independent standard Gaussian vectors. -/
def gaussianHalfSum {p : ℕ} (z : Vector p × Vector p) : Vector p :=
  fun j => (z.1 j + z.2 j) / Real.sqrt 2

theorem gaussianHalfSum_preserving (p : ℕ) :
    MeasurePreserving (gaussianHalfSum (p := p))
      ((standardGaussian p).prod (standardGaussian p)) (standardGaussian p) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin p)
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin p)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  have hp := measurePreserving_pi (fun _ : Fin p => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ => gaussianReal 0 1) (fun _ => scalar_half_sum_preserving)
  have hh := hp.comp (he.symm e)
  convert hh using 1

/-- Equal-half Gaussian addition holds for every actual measurable test. -/
theorem integral_gaussianHalfSum {p : ℕ} (f : Vector p → ℝ) (hf : Measurable f) :
    (∫ z, f (gaussianHalfSum z) ∂(standardGaussian p).prod (standardGaussian p)) =
      ∫ g, f g ∂standardGaussian p := by
  have hh := (gaussianHalfSum_preserving p).map_eq
  calc
    _ = ∫ g, f g ∂Measure.map gaussianHalfSum ((standardGaussian p).prod (standardGaussian p)) :=
      (integral_map (gaussianHalfSum_preserving p).measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [hh]

end
end RectangleCLT.Companion

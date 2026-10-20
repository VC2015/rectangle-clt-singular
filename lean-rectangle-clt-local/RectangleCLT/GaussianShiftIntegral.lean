import RectangleCLT.GaussianTriple
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of concrete Gaussian-shift integrals with
integrable Gaussian weights, including linear and quadratic polynomial weights. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

theorem hasDerivAt_weighted_gaussian_shift_integral {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (x y : Vector p)
    (W G D : Vector p → ℝ) (hW : Integrable W (standardGaussian p))
    (hG : Measurable G) (hD : Measurable D) (C₀ C₁ : ℝ)
    (hGbound : ∀ u, ‖G u‖ ≤ C₀) (hDbound : ∀ u, ‖D u‖ ≤ C₁)
    (hderiv : ∀ u t, HasDerivAt (fun r => G (FaceSmoother.line u y r))
      (D (FaceSmoother.line u y t)) t) :
    HasDerivAt
      (fun t => ∫ z, W z * G (A.mulVec z + FaceSmoother.line x y t) ∂standardGaussian p)
      (∫ z, W z * D (A.mulVec z + x) ∂standardGaussian p) 0 := by
  have hinput (t : ℝ) : Measurable (fun z : Vector p => A.mulVec z + FaceSmoother.line x y t) :=
    (measurable_mulVec A).add measurable_const
  have hint : Integrable (fun z => W z * G (A.mulVec z + x)) (standardGaussian p) := by
    simpa only [mul_comm] using hW.bdd_mul
      ((hG.comp ((measurable_mulVec A).add measurable_const)).aestronglyMeasurable)
      ⟨C₀, fun z => hGbound _⟩
  have hbound : Integrable (fun z => ‖W z‖ * C₁) (standardGaussian p) := hW.norm.mul_const C₁
  have hline (z : Vector p) (t : ℝ) :
      A.mulVec z + FaceSmoother.line x y t = FaceSmoother.line (A.mulVec z + x) y t := by
    ext j
    simp only [FaceSmoother.line, Pi.add_apply]
    ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := standardGaussian p) (bound := fun z => ‖W z‖ * C₁) (ε := 1)
    (F := fun t z => W z * G (A.mulVec z + FaceSmoother.line x y t))
    (F' := fun t z => W z * D (A.mulVec z + FaceSmoother.line x y t))
    (x₀ := (0 : ℝ)) (by norm_num)
    (Filter.Eventually.of_forall (fun t =>
      hW.aestronglyMeasurable.mul ((hG.comp (hinput t)).aestronglyMeasurable)))
    (by simpa only [FaceSmoother.line_zero] using hint)
    (hW.aestronglyMeasurable.mul
      ((hD.comp ((measurable_mulVec A).add measurable_const)).aestronglyMeasurable))
    (ae_of_all _ (fun z t _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hDbound _) (norm_nonneg _))) hbound
    (ae_of_all _ (fun z t _ => by
      simpa only [hline] using (hderiv (A.mulVec z + x) t).const_mul (W z)))
  simpa only [FaceSmoother.line_zero] using hd.2

end RectangleCLT

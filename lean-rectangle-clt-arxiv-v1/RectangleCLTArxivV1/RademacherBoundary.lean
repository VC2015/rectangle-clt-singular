import RectangleCLTCompanion.SplitV4.Printed.CubeBoundary
import RectangleCLTCompanion.SplitV4.IntrinsicCubeMaximum

/-!
Lemma C.1, frozen main source 5900–5919. The reused printed proof includes
the unique-face argument, generic threshold perturbation and positive-radius
limit for repeated faces. Both endpoints use the actual uniform sign cube.
-/
namespace RectangleCLTArxivV1

open MeasureTheory RectangleCLT.Companion.SplitV4
open scoped BigOperators

set_option autoImplicit false

theorem lemma_C1_rademacher_boundary {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b σ : ℝ)
    (hh : 0 ≤ h) (hσ : 0 < σ ^ 2)
    (hcoeff : ∀ α i, |B α i| ≤ b)
    (hrow : ∀ α, σ ^ 2 ≤ ∑ i, (B α i) ^ 2) :
    (cubeUniformLaw n).real {x | t ≤ affineCubeMaximum B a x ∧
      affineCubeMaximum B a x ≤ t + h} ≤
      (h + 8 * b) / σ ^ 2 * ∫ x, positiveLinearMaximum B x ∂cubeUniformLaw n :=
  Printed.intrinsic_cube_boundary_printed B a t h b (σ ^ 2) hh hσ hcoeff hrow

theorem lemma_C1_rademacher_maximum {m n : ℕ} (B : Fin m → Fin n → ℝ)
    (hrow : ∀ α, (∑ i, B α i ^ 2) ≤ 1) :
    (∫ x, positiveLinearMaximum B x ∂cubeUniformLaw n) ≤
      Real.sqrt (2 * Real.log ((m : ℝ) + 1)) := by
  rw [integral_cubeUniformLaw_eq_avg]
  exact intrinsicCubeMean_le_sqrt_log B hrow

end RectangleCLTArxivV1

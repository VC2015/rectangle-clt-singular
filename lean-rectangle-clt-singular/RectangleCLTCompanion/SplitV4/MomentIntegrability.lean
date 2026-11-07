import RectangleCLT.Statement
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Positivity

/-! Genuine first moments and vector centering from the coordinate fourth
moments in Appendix G. The arguments include the empty coordinate space and
do not impose a distributional or covariance hypothesis. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem abs_le_one_add_fourth (x : ℝ) : |x| ≤ 1 + x ^ 4 := by
  have ha := sq_abs x
  nlinarith [sq_nonneg (x ^ 2 - 1 / 2), sq_nonneg (|x| - 1 / 2)]

theorem vector_norm_le_one_add_sum_fourths {p : ℕ} (x : Vector p) :
    ‖x‖ ≤ 1 + ∑ j, x j ^ 4 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ∑ j, x j ^ 4)).mpr
  intro j
  rw [Real.norm_eq_abs]
  apply (abs_le_one_add_fourth (x j)).trans
  exact add_le_add_left
    (Finset.single_le_sum (f := fun k : Fin p => x k ^ 4)
      (fun k _ => by positivity) (Finset.mem_univ j)) (1 : ℝ)

/-- Finite genuine coordinate fourth moments imply a genuine Bochner first
moment of the vector, so the Slepian input adds no integrability assumption
to the manuscript's finite-fourth-moment class. -/
theorem integrable_vector_of_coordinate_fourth_moments
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Vector p) (hX : Measurable X)
    (hfourth : ∀ j, Integrable (fun ω => X ω j ^ 4) μ) : Integrable X μ := by
  apply ((integrable_const (1 : ℝ)).add
    (integrable_finset_sum _ (fun j _ => hfourth j))).mono' hX.aestronglyMeasurable
  exact ae_of_all _ (fun ω => vector_norm_le_one_add_sum_fourths (X ω))

/-- Coordinate centering is exactly vector centering when the genuine first
moment exists. The integral is tested by the bounded coordinate projections. -/
theorem integral_vector_eq_zero_of_coordinate_centered
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (X : Ω → Vector p) (hXi : Integrable X μ)
    (hcenter : ∀ j, (∫ ω, X ω j ∂μ) = 0) : (∫ ω, X ω ∂μ) = 0 := by
  ext j
  change (∫ ω, X ω ∂μ) j = 0
  have hc := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hXi
  change (∫ ω, X ω j ∂μ) = (∫ ω, X ω ∂μ) j at hc
  rw [← hc, hcenter]

theorem integrable_and_centered_of_coordinate_fourths
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Vector p) (hX : Measurable X)
    (hfourth : ∀ j, Integrable (fun ω => X ω j ^ 4) μ)
    (hcenter : ∀ j, (∫ ω, X ω j ∂μ) = 0) :
    Integrable X μ ∧ (∫ ω, X ω ∂μ) = 0 := by
  have hi := integrable_vector_of_coordinate_fourth_moments μ X hX hfourth
  exact ⟨hi, integral_vector_eq_zero_of_coordinate_centered μ X hi hcenter⟩

end

end RectangleCLT.Companion.SplitV4

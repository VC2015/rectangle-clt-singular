import RectangleCLTCompanion.SignedSurfaceGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The literal sine/angle cancellation of the printed paired ridge term. -/

open scoped InnerProductSpace

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_unit_sum_half_angle (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {ρ : ℝ} (hρ : ⟪u, v⟫_ℝ = ρ) (hlo : -1 ≤ ρ) (hhi : ρ ≤ 1) :
    ‖u + v‖ = 2 * Real.cos (Real.arccos ρ / 2) := by
  have hc := Real.cos_arccos hlo hhi
  have hs := Real.cos_two_mul (Real.arccos ρ / 2)
  have hnorm := norm_add_sq_real u v
  rw [hu, hv, hρ] at hnorm
  have hc0 : 0 ≤ Real.cos (Real.arccos ρ / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.arccos_nonneg ρ, Real.pi_nonneg])
      (by linarith [Real.arccos_le_pi ρ])
  have hcos : Real.cos (2 * (Real.arccos ρ / 2)) = ρ := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hc
  nlinarith [norm_nonneg (u + v)]

theorem norm_unit_sub_half_angle (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {ρ : ℝ} (hρ : ⟪u, v⟫_ℝ = ρ) (hlo : -1 ≤ ρ) (hhi : ρ ≤ 1) :
    ‖u - v‖ = 2 * Real.sin (Real.arccos ρ / 2) := by
  have hc := Real.cos_arccos hlo hhi
  have hs := Real.cos_two_mul (Real.arccos ρ / 2)
  have ht := Real.sin_sq_add_cos_sq (Real.arccos ρ / 2)
  have hnorm := norm_sub_sq_real u v
  rw [hu, hv, hρ] at hnorm
  have hs0 : 0 ≤ Real.sin (Real.arccos ρ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [Real.arccos_nonneg ρ])
      (by linarith [Real.arccos_le_pi ρ, Real.pi_nonneg])
  have hcos : Real.cos (2 * (Real.arccos ρ / 2)) = ρ := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hc
  nlinarith [norm_nonneg (u - v)]

theorem angular_pair_coefficient (u v z : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {ρ : ℝ} (hρ : ⟪u, v⟫_ℝ = ρ) (hlo : -1 < ρ) (hhi : ρ < 1) :
    (1 - ρ) * |⟪u, z⟫_ℝ + ⟪v, z⟫_ℝ| / Real.sin (Real.arccos ρ) ≤
      Real.arccos ρ * ‖z‖ := by
  let α := Real.arccos ρ
  have hα0 : 0 < α := Real.arccos_pos.mpr hhi
  have hαπ : α < Real.pi := by
    simpa only [Real.arccos_neg_one] using
      (Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ -1) hlo hhi.le)
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have hc := Real.cos_arccos hlo.le hhi.le
  have hc2 := Real.cos_two_mul (α / 2)
  have hs2 := Real.sin_two_mul (α / 2)
  have htrig := Real.sin_sq_add_cos_sq (α / 2)
  have hid : (1 - ρ) * ‖u + v‖ / Real.sin α = 2 * Real.sin (α / 2) := by
    rw [norm_unit_sum_half_angle u v hu hv hρ hlo.le hhi.le]
    apply (div_eq_iff hsin.ne').mpr
    have he : 2 * (α / 2) = α := by ring
    rw [he] at hc2 hs2
    change Real.cos α = ρ at hc
    change (1 - ρ) * (2 * Real.cos (α / 2)) = _
    have hr : 1 - ρ = 2 * Real.sin (α / 2) ^ 2 := by nlinarith
    rw [hr, hs2]
    ring
  have hab : |⟪u, z⟫_ℝ + ⟪v, z⟫_ℝ| ≤ ‖u + v‖ * ‖z‖ := by
    rw [← inner_add_left]
    exact abs_real_inner_le_norm _ _
  calc
    _ ≤ (1 - ρ) * (‖u + v‖ * ‖z‖) / Real.sin α :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hab (by linarith)) hsin.le
    _ = (2 * Real.sin (α / 2)) * ‖z‖ := by rw [← hid]; ring
    _ ≤ α * ‖z‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith [Real.sin_le (show 0 ≤ α / 2 by positivity)]

end
end RectangleCLT.Companion.SplitV4.Printed

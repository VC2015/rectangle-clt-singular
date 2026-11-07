import RectangleCLTCompanion.SplitV4.Printed.RidgeSector
import RectangleCLTCompanion.SplitV4.Printed.RidgeAngular
import RectangleCLTCompanion.SignedSurfacePolyhedron

/-! The angular sector is inside the actual positive normal cone. Thus its
points have the same metric-projection base as the printed ridge event. -/

open MeasureTheory Set
open scoped InnerProductSpace
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem planeSector_radius {α η : ℝ} {st : ℝ × ℝ} (hst : st ∈ planeSector α η) :
    0 < planeRadius st ∧ planeRadius st < η := hst.2.1

theorem ridgeDisplacement_norm (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) (st : ℝ × ℝ) :
    ‖SignedSurface.ridgeDisplacement u v st‖ = planeRadius st := by
  have hs := norm_add_sq_real
    (st.1 • SignedSurface.bisector u v) (st.2 • SignedSurface.differenceDirection u v)
  have he := SignedSurface.norm_bisector u v hp
  have hf := SignedSurface.norm_differenceDirection u v hm
  have hef := SignedSurface.inner_bisector_differenceDirection u v (hu.trans hv.symm)
  simp only [norm_smul, Real.norm_eq_abs, he, hf, mul_one, inner_smul_left,
    inner_smul_right, conj_trivial, hef, mul_zero, zero_mul, add_zero, sq_abs] at hs
  have hr : planeRadius st ^ 2 = st.1 ^ 2 + st.2 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  change ‖st.1 • SignedSurface.bisector u v + st.2 • SignedSurface.differenceDirection u v‖ = _
  have hr0 : 0 ≤ planeRadius st := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (st.1 • SignedSurface.bisector u v +
    st.2 • SignedSurface.differenceDirection u v)]

theorem planeSector_positive_coefficients (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {ρ : ℝ} (hρ : ⟪u, v⟫_ℝ = ρ) (hlo : -1 < ρ) (hhi : ρ < 1)
    {η : ℝ} {st : ℝ × ℝ} (hst : st ∈ planeSector (Real.arccos ρ) η) :
    0 < st.1 / ‖u + v‖ + st.2 / ‖u - v‖ ∧
      0 < st.1 / ‖u + v‖ - st.2 / ‖u - v‖ := by
  let α := Real.arccos ρ
  let r := planeRadius st
  let θ := (polarCoord st).2
  have hα : 0 < α := Real.arccos_pos.mpr hhi
  have hαπ : α < Real.pi := by
    simpa only [Real.arccos_neg_one] using
      (Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ -1) hlo hhi.le)
  have hr : 0 < r := hst.2.1.1
  have hθ : -α / 2 < θ ∧ θ < α / 2 := hst.2.2
  have hsc : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hαπ
  have hsh : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith [Real.pi_pos])
  have hch : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hstrep : st = polarCoord.symm (r, θ) := (polarCoord.left_inv hst.1).symm
  have hsum : st.1 / ‖u + v‖ + st.2 / ‖u - v‖ =
      r * Real.sin (α / 2 + θ) / Real.sin α := by
    rw [norm_unit_sum_half_angle u v hu hv hρ hlo.le hhi.le,
      norm_unit_sub_half_angle u v hu hv hρ hlo.le hhi.le]
    change st.1 / (2 * Real.cos (α / 2)) + st.2 / (2 * Real.sin (α / 2)) = _
    rw [hstrep]
    simp only [polarCoord_symm_apply, Real.sin_add]
    have he : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
      convert Real.sin_two_mul (α / 2) using 1 <;> congr 1 <;> ring
    rw [he]
    field_simp
    <;> ring
  have hsub : st.1 / ‖u + v‖ - st.2 / ‖u - v‖ =
      r * Real.sin (α / 2 - θ) / Real.sin α := by
    rw [norm_unit_sum_half_angle u v hu hv hρ hlo.le hhi.le,
      norm_unit_sub_half_angle u v hu hv hρ hlo.le hhi.le]
    change st.1 / (2 * Real.cos (α / 2)) - st.2 / (2 * Real.sin (α / 2)) = _
    rw [hstrep]
    simp only [polarCoord_symm_apply, Real.sin_sub]
    have he : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
      convert Real.sin_two_mul (α / 2) using 1 <;> congr 1 <;> ring
    rw [he]
    field_simp
    <;> ring
  rw [hsum, hsub]
  exact ⟨div_pos (mul_pos hr (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2]))) hsc,
    div_pos (mul_pos hr (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.2]) (by linarith [hθ.1]))) hsc⟩

theorem planeSector_maps_into_cone (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {ρ : ℝ} (hρ : ⟪u, v⟫_ℝ = ρ) (hlo : -1 < ρ) (hhi : ρ < 1)
    {η : ℝ} {st : ℝ × ℝ} (hst : st ∈ planeSector (Real.arccos ρ) η) :
    SignedSurface.ridgeDisplacement u v st ∈ SignedSurface.normalConePair u v := by
  have hh := planeSector_positive_coefficients u v hu hv hρ hlo hhi hst
  exact ⟨_, _, hh.1.le, hh.2.le, SignedSurface.ridgeDisplacement_expansion u v st⟩

end
end RectangleCLT.Companion.SplitV4.Printed

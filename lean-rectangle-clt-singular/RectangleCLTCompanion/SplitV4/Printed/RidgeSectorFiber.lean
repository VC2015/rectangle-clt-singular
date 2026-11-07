import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorGeometry
import RectangleCLTCompanion.SignedSurfaceTubes

/-! The printed adaptive sector fiber: the radius stays within 3/4 and 5/4
of its base value, the normal density loses at most exp(-9/32), and exact
sector area supplies the angular factor. -/

open MeasureTheory Set
open scoped InnerProductSpace
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem adaptive_sector_point (R : E → ℝ) (hR : ∀ x, 1 ≤ R x)
    (hadd : ∀ x y, R (x + y) ≤ R x + ‖y‖) (u v x z : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    (hz : ‖z‖ ≤ R x) {α : ℝ} {st : ℝ × ℝ}
    (hst : st ∈ planeSector α (1 / (4 * R x))) :
    (3 * R x / 4) ^ 3 * Real.exp (-(9 : ℝ) / 32) * SignedSurface.gaussianKernel z ≤
      R (x + SignedSurface.ridgeDisplacement u v st) ^ 3 *
        SignedSurface.gaussianKernel (z + SignedSurface.ridgeDisplacement u v st) := by
  let y := SignedSurface.ridgeDisplacement u v st
  have hRx : 0 < R x := lt_of_lt_of_le zero_lt_one (hR x)
  have hden : 0 < 4 * R x := by positivity
  have hyn : ‖y‖ ≤ 1 / (4 * R x) :=
    (ridgeDisplacement_norm u v hu hv hp hm st).le.trans (planeSector_radius hst).2.le
  have hprod : R x * ‖y‖ ≤ (1 : ℝ) / 4 := by
    have hh := mul_le_mul_of_nonneg_left hyn hRx.le
    have he : R x * (1 / (4 * R x)) = (1 : ℝ) / 4 := by field_simp; ring
    exact hh.trans_eq he
  have hyquarter : ‖y‖ ≤ (1 : ℝ) / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right (hR x) (norm_nonneg y)]
  have hbase : R x ≤ R (x + y) + ‖y‖ := by
    have hh := hadd (x + y) (-y)
    simpa only [add_neg_cancel_right, norm_neg] using hh
  have hRlow : 3 * R x / 4 ≤ R (x + y) := by
    nlinarith [hR x]
  have hpow : (3 * R x / 4) ^ 3 ≤ R (x + y) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hRlow 3
  have hinner : ⟪z, y⟫_ℝ ≤ (1 : ℝ) / 4 := by
    calc
      _ ≤ |⟪z, y⟫_ℝ| := le_abs_self _
      _ ≤ ‖z‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ ≤ R x * ‖y‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ _ := hprod
  have hpdf : Real.exp (-(9 : ℝ) / 32) * SignedSurface.gaussianKernel z ≤
      SignedSurface.gaussianKernel (z + y) := by
    unfold SignedSurface.gaussianKernel
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [norm_add_sq_real z y, norm_nonneg y]
  have hpdf0 : 0 ≤ Real.exp (-(9 : ℝ) / 32) * SignedSurface.gaussianKernel z :=
    mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hpow0 : 0 ≤ R (x + y) ^ 3 := pow_nonneg (zero_le_one.trans (hR _)) _
  simpa only [mul_assoc] using mul_le_mul hpow hpdf hpdf0 hpow0

theorem adaptive_sector_fiber_lower (R : E → ℝ) (hRc : Continuous R)
    (hR : ∀ x, 1 ≤ R x) (hadd : ∀ x y, R (x + y) ≤ R x + ‖y‖)
    (u v x z : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) (hz : ‖z‖ ≤ R x)
    {α : ℝ} (hα : 0 < α) (hαπ : α ≤ Real.pi) :
    (27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32) * α * R x *
        SignedSurface.gaussianKernel z ≤
      ∫ st in planeSector α (1 / (4 * R x)),
        R (x + SignedSurface.ridgeDisplacement u v st) ^ 3 *
          SignedSurface.gaussianKernel (z + SignedSurface.ridgeDisplacement u v st) := by
  have hRx : 0 < R x := lt_of_lt_of_le zero_lt_one (hR x)
  have hi : IntegrableOn
      (fun st => R (x + SignedSurface.ridgeDisplacement u v st) ^ 3 *
        SignedSurface.gaussianKernel (z + SignedSurface.ridgeDisplacement u v st))
      (planeSector α (1 / (4 * R x))) :=
    continuous_integrableOn_planeSector (by fun_prop) _ _
  have hc : IntegrableOn (fun _ : ℝ × ℝ =>
      (3 * R x / 4) ^ 3 * Real.exp (-(9 : ℝ) / 32) * SignedSurface.gaussianKernel z)
      (planeSector α (1 / (4 * R x))) :=
    continuous_integrableOn_planeSector continuous_const _ _
  have hh := integral_mono_ae hc hi
    ((ae_restrict_mem (isOpen_planeSector α _).measurableSet).mono
      (fun st hst => adaptive_sector_point R hR hadd u v x z hu hv hp hm hz hst))
  rw [setIntegral_const, planeSector_real_area hα hαπ (by positivity), smul_eq_mul] at hh
  convert hh using 1
  field_simp
  <;> ring

end
end RectangleCLT.Companion.SplitV4.Printed

import RectangleCLTCompanion.SplitV4.Printed.PolarPlane
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Genuine planar sectors and the angular cancellation in the printed
two-face tube argument. The sector area is obtained from the polar Jacobian. -/

open MeasureTheory Set
open scoped InnerProductSpace

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def planeSector (α η : ℝ) : Set (ℝ × ℝ) :=
  polarCoord.source ∩ polarCoord ⁻¹' (Ioo (0 : ℝ) η ×ˢ Ioo (-α / 2) (α / 2))

theorem isOpen_planeSector (α η : ℝ) : IsOpen (planeSector α η) :=
  polarCoord.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_Ioo)

theorem planeSector_polar_iff {α η : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ planeSector α η ↔ p ∈ Ioo (0 : ℝ) η ×ˢ Ioo (-α / 2) (α / 2) := by
  unfold planeSector
  simp only [mem_inter_iff, mem_preimage, polarCoord.right_inv hp,
    polarCoord.map_target hp, true_and]

theorem planeSector_real_area {α η : ℝ} (hα : 0 < α) (hαπ : α ≤ Real.pi)
    (hη : 0 ≤ η) :
    (volume : Measure (ℝ × ℝ)).real (planeSector α η) = α * η ^ 2 / 2 := by
  let D := Ioo (0 : ℝ) η ×ˢ Ioo (-α / 2) (α / 2)
  have hD : MeasurableSet D := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : D ⊆ polarCoord.target := by
    intro p hp
    change (0 < p.1 ∧ p.1 < η) ∧ (-α / 2 < p.2 ∧ p.2 < α / 2) at hp
    refine ⟨hp.1.1, ?_, ?_⟩ <;> linarith [hp.2.1, hp.2.2, Real.pi_pos]
  have hi : (∫ r in Ioo (0 : ℝ) η, r) = η ^ 2 / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hη,
      integral_id]
    simp
  calc
    _ = ∫ z : ℝ × ℝ, (planeSector α η).indicator (fun _ => (1 : ℝ)) z :=
      (integral_indicator_one (isOpen_planeSector α η).measurableSet).symm
    _ = ∫ p in polarCoord.target, p.1 •
        (planeSector α η).indicator (fun _ => (1 : ℝ)) (polarCoord.symm p) :=
      (integral_comp_polarCoord_symm _).symm
    _ = ∫ p in polarCoord.target, D.indicator (fun p : ℝ × ℝ => p.1) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      dsimp only
      have he := planeSector_polar_iff (α := α) (η := η) hp
      by_cases hd : p ∈ D
      · simp only [Set.indicator_of_mem hd, Set.indicator_of_mem (he.mpr hd),
          smul_eq_mul, mul_one]
      · simp only [Set.indicator_of_not_mem hd, Set.indicator_of_not_mem
          (fun h => hd (he.mp h)), smul_eq_mul, mul_zero]
    _ = ∫ p in D, p.1 := by
      rw [integral_indicator hD, Measure.restrict_restrict hD, inter_eq_left.mpr hsub]
    _ = (∫ r in Ioo (0 : ℝ) η, r) * ∫ θ in Ioo (-α / 2) (α / 2), (1 : ℝ) := by
      rw [← setIntegral_prod_mul]
      simp only [D, mul_one]
      rfl
    _ = α * η ^ 2 / 2 := by
      rw [hi]
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
        univ_inter, Real.volume_real_Ioo_of_le (by linarith : -α / 2 ≤ α / 2),
        smul_eq_mul]
      ring

theorem abs_fst_le_planeRadius (st : ℝ × ℝ) : |st.1| ≤ planeRadius st := by
  have hh : planeRadius st ^ 2 = st.1 ^ 2 + st.2 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hr : 0 ≤ planeRadius st := Real.sqrt_nonneg _
  nlinarith [sq_abs st.1, abs_nonneg st.1, sq_nonneg st.2]

theorem abs_snd_le_planeRadius (st : ℝ × ℝ) : |st.2| ≤ planeRadius st := by
  have hh : planeRadius st ^ 2 = st.1 ^ 2 + st.2 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hr : 0 ≤ planeRadius st := Real.sqrt_nonneg _
  nlinarith [sq_abs st.2, abs_nonneg st.2, sq_nonneg st.1]

theorem planeSector_subset_square (α η : ℝ) :
    planeSector α η ⊆ Icc (-η) η ×ˢ Icc (-η) η := by
  intro st hst
  have hh : planeRadius st < η := hst.2.1.2
  exact ⟨abs_le.mp ((abs_fst_le_planeRadius st).trans hh.le),
    abs_le.mp ((abs_snd_le_planeRadius st).trans hh.le)⟩

theorem continuous_integrableOn_planeSector {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (α η : ℝ) : IntegrableOn f (planeSector α η) :=
  (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (planeSector_subset_square α η)

end
end RectangleCLT.Companion.SplitV4.Printed

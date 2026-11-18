import RectangleCLTArxivV1.SupplementalHSphericalPolar
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Data.Complex.FiniteDimensional

/-! Exact Gaussian weights of actual planar angular sectors. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set Metric
noncomputable section

/-- A planar sector specified by the ordinary principal argument. -/
def supplementalHPlanarSector (a b : ℝ) : Set ℂ :=
  Complex.arg ⁻¹' Ioo a b

theorem supplementalHPlanarSector_measurable (a b : ℝ) :
    MeasurableSet (supplementalHPlanarSector a b) :=
  Complex.measurable_arg measurableSet_Ioo

theorem supplementalHPlanarSector_dilation (a b r : ℝ) (hr : 0 < r) (z : ℂ) :
    r • z ∈ supplementalHPlanarSector a b ↔ z ∈ supplementalHPlanarSector a b := by
  change Complex.arg ((r : ℂ)*z) ∈ Ioo a b ↔ Complex.arg z ∈ Ioo a b
  rw [Complex.arg_real_mul z hr]

/-- The unnormalized Gaussian area of a planar sector is exactly its
angular width. The open boundary rays have their usual zero area. -/
theorem supplementalH_planar_sector_gaussian (a b : ℝ)
    (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi) (hab : a ≤ b) :
    (∫ z in supplementalHPlanarSector a b, Real.exp (-‖z‖^2/2)) = b-a := by
  rw [← integral_indicator (supplementalHPlanarSector_measurable a b),
    ← Complex.integral_comp_polarCoord_symm]
  have he (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      p.1 • (supplementalHPlanarSector a b).indicator
          (fun z : ℂ => Real.exp (-‖z‖^2/2)) (Complex.polarCoord.symm p) =
        (p.1*Real.exp (-p.1^2/2)) * (Ioo a b).indicator (fun _ => (1 : ℝ)) p.2 := by
    have harg : Complex.arg (Complex.polarCoord.symm p) = p.2 := by
      have hh := congrArg Prod.snd (Complex.polarCoord.right_inv hp)
      simpa only [Complex.polarCoord_apply] using hh
    have hnorm := Complex.norm_polarCoord_symm p
    by_cases h : p.2 ∈ Ioo a b
    · have hm : Complex.polarCoord.symm p ∈ supplementalHPlanarSector a b := by
        simpa only [supplementalHPlanarSector, mem_preimage, harg] using h
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem h, hnorm,
        abs_of_pos hp.1, smul_eq_mul, mul_one]
    · have hm : Complex.polarCoord.symm p ∉ supplementalHPlanarSector a b := by
        simpa only [supplementalHPlanarSector, mem_preimage, harg] using h
      rw [Set.indicator_of_not_mem hm, Set.indicator_of_not_mem h, smul_zero, mul_zero]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet he]
  change (∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    (p.1*Real.exp (-p.1^2/2)) * (Ioo a b).indicator (fun _ => (1 : ℝ)) p.2) = _
  rw [Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r : ℝ => r*Real.exp (-r^2/2))
      ((Ioo a b).indicator (fun _ => (1 : ℝ))) (Ioi 0) (Ioo (-Real.pi) Real.pi),
    supplementalH_integral_radial_two, one_mul, setIntegral_indicator measurableSet_Ioo]
  have hs : Ioo a b ⊆ Ioo (-Real.pi) Real.pi := by
    intro x hx
    exact ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
  rw [Set.inter_eq_right.mpr hs]
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
    Real.volume_real_Ioo_of_le hab]

/-- In particular the sector of width `arccos c` has exactly that
unnormalized Gaussian area, including the two degenerate endpoint angles. -/
theorem supplementalH_planar_arccos_sector_gaussian (c : ℝ) :
    (∫ z in supplementalHPlanarSector 0 (Real.arccos c),
      Real.exp (-‖z‖^2/2)) = Real.arccos c := by
  simpa only [sub_zero] using supplementalH_planar_sector_gaussian 0 (Real.arccos c)
    (by linarith [Real.pi_pos]) (Real.arccos_le_pi c) (Real.arccos_nonneg c)

/-- The polar angular measure is exactly ordinary arc length on each
principal-argument interval of the Euclidean unit circle. -/
theorem supplementalH_circle_arc_area (a b : ℝ)
    (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi) (hab : a ≤ b) :
    (volume : Measure ℂ).toSphere.real
      (supplementalHSphericalSection (supplementalHPlanarSector a b)) = b-a := by
  rw [← supplementalH_planar_cone_gaussian_mass volume Complex.finrank_real_complex
    (supplementalHPlanarSector a b) (supplementalHPlanarSector_measurable a b)
    (fun r hr z => supplementalHPlanarSector_dilation a b r hr z)]
  exact supplementalH_planar_sector_gaussian a b ha hb hab

theorem supplementalH_circle_arccos_arc_area (c : ℝ) :
    (volume : Measure ℂ).toSphere.real
      (supplementalHSphericalSection (supplementalHPlanarSector 0 (Real.arccos c))) =
      Real.arccos c := by
  simpa only [sub_zero] using supplementalH_circle_arc_area 0 (Real.arccos c)
    (by linarith [Real.pi_pos]) (Real.arccos_le_pi c) (Real.arccos_nonneg c)

end
end RectangleCLTArxivV1

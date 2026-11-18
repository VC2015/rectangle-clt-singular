import RectangleCLTArxivV1.PairedGaussianEndpointSmoothing

/-! Actual two-coupling transfer with the original intrinsic Gaussian width.
The perturbations in either coupling may be dependent. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion

theorem rectangleError_le_of_two_couplings_intrinsic
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p : ℕ}
    (hp : 1 ≤ p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (W WT : Ω → Vector p) (Z ZT : E → Vector p)
    (hW : Measurable W) (hZ : Measurable Z)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hZlaw : ν.map Z = gaussianLaw A)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {B r₁ r₂ ε₁ ε₂ : ℝ} (hr : 0 < r₁ + r₂)
    (hcompare : ∀ R : Rect p,
      |μ.real (WT ⁻¹' R.carrier) - ν.real (ZT ⁻¹' R.carrier)| ≤ B)
    (hbadW : μ.real {ω | r₁ < ‖W ω - WT ω‖} ≤ ε₁)
    (hbadZ : ν.real {z | r₂ < ‖ZT z - Z z‖} ≤ ε₂)
    (R : Rect p) :
    rectangleError μ W A R ≤ B +
      2 * (r₁ + r₂) * gaussianMaximumMean A + ε₁ + ε₂ := by
  apply rectangleError_le_of_closedBox hp μ W hW A _ R
  intro lo hi
  let d := r₁ + r₂
  have hpZ (t : ℝ) := probability_eq_gaussian_of_map_eq ν Z hZ A hZlaw (shiftedBox lo hi t)
  have huW := probability_shiftedBox_le_add_bad μ W WT lo hi 0 r₁ ε₁ hbadW
  have huZ := probability_shiftedBox_le_add_bad ν ZT Z lo hi r₁ r₂ ε₂ hbadZ
  have huC := (abs_le.mp (hcompare (shiftedBox lo hi r₁))).2
  have huG := gaussian_probability_shiftedBox_intrinsic hp A hdiag lo hi hr
  have hlW := probability_shiftedBox_le_add_bad μ WT W lo hi (-r₁) r₁ ε₁
    (by simpa only [norm_sub_rev] using hbadW)
  have hlZ := probability_shiftedBox_le_add_bad ν Z ZT lo hi (-d) r₂ ε₂
    (by simpa only [norm_sub_rev] using hbadZ)
  have hlC := (abs_le.mp (hcompare (shiftedBox lo hi (-r₁)))).1
  have hlG := gaussian_probability_le_contractedBox_intrinsic hp A hdiag lo hi hr
  have hneg : -d + r₂ = -r₁ := by dsimp only [d]; ring
  simp only [zero_add, shiftedBox_zero] at huW
  rw [hpZ (r₁ + r₂)] at huZ
  rw [neg_add_cancel, shiftedBox_zero] at hlW
  rw [hneg] at hlZ
  rw [hpZ (-d)] at hlZ
  dsimp only [d] at hlZ
  change |μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) -
    (gaussianLaw A).real (Rect.closedBox lo hi).carrier| ≤ _
  apply abs_le.mpr
  constructor <;> linarith


end RectangleCLTArxivV1

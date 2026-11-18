import RectangleCLTArxivV1.CapFourierKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The one- and two-dimensional Gaussian Fourier majorants. Completing
one square makes the angular loss exactly the inverse square root of the
projected covariance determinant. -/

namespace RectangleCLTArxivV1
open MeasureTheory
noncomputable section

def capGaussianExponent : ℝ := 1/Real.pi^2

def capSingleMajorant (t : ℝ) : ℝ := Real.exp (-capGaussianExponent*t^2)

def capPairMajorant (ρ : ℝ) (t : ℝ × ℝ) : ℝ :=
  Real.exp (-capGaussianExponent*(t.1^2+2*ρ*t.1*t.2+t.2^2))

theorem capGaussianExponent_pos : 0 < capGaussianExponent := by unfold capGaussianExponent; positivity

theorem integrable_capSingleMajorant : Integrable capSingleMajorant volume :=
  integrable_exp_neg_mul_sq capGaussianExponent_pos

theorem capSingleMajorant_nonneg (t : ℝ) : 0 ≤ capSingleMajorant t := (Real.exp_pos _).le

theorem capSingleMajorant_le_one (t : ℝ) : capSingleMajorant t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr capGaussianExponent_pos.le) (sq_nonneg _)

theorem integral_capSingleMajorant : (∫ t, capSingleMajorant t) =
    Real.sqrt (Real.pi/capGaussianExponent) := integral_gaussian capGaussianExponent

theorem capPairMajorant_factor (ρ : ℝ) (x y : ℝ) :
    capPairMajorant ρ (x,y) =
      capSingleMajorant (y+ρ*x)*Real.exp (-(capGaussianExponent*(1-ρ^2))*x^2) := by
  rw [capPairMajorant,capSingleMajorant,← Real.exp_add]
  congr 1
  ring

theorem capPairMajorant_nonneg (ρ : ℝ) (t : ℝ × ℝ) : 0 ≤ capPairMajorant ρ t :=
  (Real.exp_pos _).le

theorem capPairMajorant_le_one {ρ : ℝ} (hρ : ρ^2 < 1) (t : ℝ × ℝ) :
    capPairMajorant ρ t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hquad : 0 ≤ t.1^2+2*ρ*t.1*t.2+t.2^2 := by
    have hp := mul_nonneg (show 0 ≤ 1-ρ^2 by linarith) (sq_nonneg t.1)
    nlinarith [sq_nonneg (t.2+ρ*t.1)]
  simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg capGaussianExponent_pos.le hquad)

theorem integral_capPairMajorant_inner {ρ : ℝ} (x : ℝ) :
    (∫ y, capPairMajorant ρ (x,y)) =
      Real.exp (-(capGaussianExponent*(1-ρ^2))*x^2) * Real.sqrt (Real.pi/capGaussianExponent) := by
  simp_rw [capPairMajorant_factor]
  rw [integral_mul_const,integral_add_right_eq_self,integral_capSingleMajorant]
  ring

theorem integrable_capPairMajorant {ρ : ℝ} (hρ : ρ^2 < 1) :
    Integrable (capPairMajorant ρ) volume := by
  have ha : 0 < capGaussianExponent*(1-ρ^2) := mul_pos capGaussianExponent_pos (by linarith)
  have hm : Measurable (capPairMajorant ρ) := by unfold capPairMajorant; fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun x => by
      simp_rw [capPairMajorant_factor]
      exact (((measurePreserving_add_right volume (ρ*x)).integrable_comp
        integrable_capSingleMajorant.aestronglyMeasurable).mpr integrable_capSingleMajorant).mul_const _)
  · have hi := (integrable_exp_neg_mul_sq ha).mul_const (Real.sqrt (Real.pi/capGaussianExponent))
    convert hi using 1
    ext x
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (capPairMajorant_nonneg ρ _),
      integral_capPairMajorant_inner]

theorem integral_capPairMajorant {ρ : ℝ} (hρ : ρ^2 < 1) :
    (∫ t, capPairMajorant ρ t) =
      (Real.pi/capGaussianExponent)/Real.sqrt (1-ρ^2) := by
  have hpos : 0 < 1-ρ^2 := by linarith
  have hga := capGaussianExponent_pos
  have heq : Real.pi/(capGaussianExponent*(1-ρ^2)) =
      (Real.pi/capGaussianExponent)/(1-ρ^2) := by rw [div_div]
  change (∫ t : ℝ × ℝ, capPairMajorant ρ t ∂((volume : Measure ℝ).prod volume)) = _
  rw [integral_prod _ (integrable_capPairMajorant hρ)]
  simp_rw [integral_capPairMajorant_inner]
  rw [integral_mul_const,integral_gaussian,heq,Real.sqrt_div (by positivity)]
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi/capGaussianExponent by positivity)
  calc
    _ = (Real.sqrt (Real.pi/capGaussianExponent))^2 / Real.sqrt (1-ρ^2) := by ring
    _ = _ := by rw [hs]

theorem integral_capPairMajorant_pi {ρ : ℝ} (hρ : ρ^2 < 1) :
    (∫ t, capPairMajorant ρ t) = Real.pi^3/Real.sqrt (1-ρ^2) := by
  rw [integral_capPairMajorant hρ]
  unfold capGaussianExponent
  congr 1
  field_simp
  ring

end
end RectangleCLTArxivV1

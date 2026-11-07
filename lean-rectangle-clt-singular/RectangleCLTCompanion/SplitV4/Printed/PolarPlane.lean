import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Polar integration for the two-dimensional normal sections used in the
printed adaptive-radius and ridge-sector arguments. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def planeRadius (z : ℝ × ℝ) : ℝ := Real.sqrt (z.1 ^ 2 + z.2 ^ 2)

theorem planeRadius_polar (p : ℝ × ℝ) (hp : 0 ≤ p.1) :
    planeRadius (polarCoord.symm p) = p.1 := by
  unfold planeRadius
  simp only [polarCoord_symm_apply]
  have he : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq p.2]
  rw [he, Real.sqrt_sq hp]

theorem integral_plane_radial (f : ℝ → ℝ) :
    (∫ z : ℝ × ℝ, f (planeRadius z)) =
      (2 * Real.pi) * ∫ r in Ioi (0 : ℝ), r * f r := by
  rw [← integral_comp_polarCoord_symm]
  have he : (∫ p in polarCoord.target, p.1 • f (planeRadius (polarCoord.symm p))) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, (p.1 * f p.1) * (1 : ℝ) := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    rw [planeRadius_polar p hp.1.le]
    simp
  rw [he]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    (p.1 * f p.1) * (1 : ℝ) ∂(volume : Measure ℝ).prod volume) = _
  rw [setIntegral_prod_mul (fun r : ℝ => r * f r) (fun _ : ℝ => 1)]
  simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg] : -Real.pi ≤ Real.pi),
    smul_eq_mul]
  ring

theorem integral_radial_gaussian_tail (s : ℝ) :
    (∫ r in Ioi s, r * Real.exp (-(r ^ 2) / 2)) = Real.exp (-(s ^ 2) / 2) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -Real.exp (-(y ^ 2) / 2))
      (x * Real.exp (-(x ^ 2) / 2)) x := by
    convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).neg using 1 <;> simp only [id_eq] <;> ring
  have hi : Integrable (fun r : ℝ => r * Real.exp (-(r ^ 2) / 2)) := by
    convert (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)) using 1
    congr 1
    funext r
    congr 2
    ring
  have ht : Tendsto (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
        (by norm_num : (-(1 / 2 : ℝ)) < 0))
    convert hh.neg using 1
    · funext y
      congr 2
      ring
    · simp
  simpa only [zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi.integrableOn ht

end
end RectangleCLT.Companion.SplitV4.Printed

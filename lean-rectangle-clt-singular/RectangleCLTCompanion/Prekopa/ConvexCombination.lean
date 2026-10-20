import RectangleCLTCompanion.Prekopa.PrekopaLeindler
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The convex-combination form of the vendored Prékopa--Leindler inequality.
This wrapper changes variables in the actual Lebesgue integrals. -/

open MeasureTheory

namespace RectangleCLT.Companion.Prekopa

noncomputable section

lemma lintegral_comp_inv_smul {d : ℕ} (f : (Fin d → ℝ) → ENNReal)
    (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    (∫⁻ x, f (a⁻¹ • x)) = ENNReal.ofReal (a ^ d) * ∫⁻ x, f x := by
  let T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := a⁻¹ • LinearMap.id
  have hdet : LinearMap.det T = a⁻¹ ^ d := by
    simp [T, LinearMap.det_smul, LinearMap.det_id]
  have hT : Measurable T := by
    change Measurable (fun x : Fin d → ℝ => a⁻¹ • x)
    fun_prop
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := T) (by rw [hdet]; exact pow_ne_zero _ (inv_ne_zero ha.ne'))
  have hscale : |(LinearMap.det T)⁻¹| = a ^ d := by
    rw [hdet, ← inv_pow, inv_inv, abs_of_pos (pow_pos ha _)]
  rw [hscale] at hm
  have hh := lintegral_map hf hT (μ := volume)
  rw [hm, lintegral_smul_measure] at hh
  exact hh.symm

/-- Standard convex-combination form, valid for measurable extended
nonnegative functions without a finiteness hypothesis. -/
theorem prekopa_leindler_convex
    {d : ℕ} {θ : ℝ} {f g h : (Fin (d + 1) → ℝ) → ENNReal}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ ≤ ∫⁻ x, h x := by
  have ha : 0 < 1 - θ := by linarith
  let F := fun x => f ((1 - θ)⁻¹ • x)
  let G := fun x => g (θ⁻¹ • x)
  have hF : Measurable F := by fun_prop
  have hG : Measurable G := by fun_prop
  have hpoint (x y : Fin (d + 1) → ℝ) :
      F x ^ (1 - θ) * G y ^ θ ≤ h (x + y) := by
    have ht := hfgh ((1 - θ)⁻¹ • x) (θ⁻¹ • y)
    simpa only [smul_smul, mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hθ0.ne', one_smul]
      using ht
  have hp := prekopa_leindler ⟨hθ0, hθ1, hF, hG, hh, hpoint⟩
  change ENNReal.ofReal ((1 - θ) ^ ((d + 1) * (1 - θ)) * θ ^ ((d + 1) * θ))⁻¹ *
    (∫⁻ x, f ((1 - θ)⁻¹ • x)) ^ (1 - θ) *
    (∫⁻ x, g (θ⁻¹ • x)) ^ θ ≤ _ at hp
  rw [lintegral_comp_inv_smul f hf ha, lintegral_comp_inv_smul g hg hθ0,
    ENNReal.mul_rpow_of_nonneg _ _ ha.le, ENNReal.mul_rpow_of_nonneg _ _ hθ0.le,
    ENNReal.ofReal_rpow_of_pos (pow_pos ha _),
    ENNReal.ofReal_rpow_of_pos (pow_pos hθ0 _)] at hp
  have hpa : ((1 - θ) ^ (d + 1)) ^ (1 - θ) =
      (1 - θ) ^ (((d : ℝ) + 1) * (1 - θ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    simp
  have hpb : (θ ^ (d + 1)) ^ θ = θ ^ (((d : ℝ) + 1) * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ0.le]
    simp
  rw [hpa, hpb] at hp
  let c := (1 - θ) ^ (((d : ℝ) + 1) * (1 - θ)) * θ ^ (((d : ℝ) + 1) * θ)
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hθ0 _)
  have hcancel : ENNReal.ofReal c⁻¹ *
      (ENNReal.ofReal ((1 - θ) ^ (((d : ℝ) + 1) * (1 - θ))) * (∫⁻ x, f x) ^ (1 - θ)) *
      (ENNReal.ofReal (θ ^ (((d : ℝ) + 1) * θ)) * (∫⁻ x, g x) ^ θ) =
      (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ := by
    calc
      _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) *
          ((∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ) := by
        dsimp [c]
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
        ring
      _ = _ := by
        rw [ENNReal.ofReal_inv_of_pos hc,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top,
          one_mul]
  exact hcancel ▸ hp

/-- Real integral form for integrable nonnegative functions. -/
theorem prekopa_leindler_integral
    {d : ℕ} {θ : ℝ} {f g h : (Fin (d + 1) → ℝ) → ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hfi : Integrable f volume) (hgi : Integrable g volume) (hhi : Integrable h volume)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h ((1 - θ) • x + θ • y)) :
    (∫ x, f x) ^ (1 - θ) * (∫ x, g x) ^ θ ≤ ∫ x, h x := by
  have ha : 0 ≤ 1 - θ := by linarith
  have hp := prekopa_leindler_convex hθ0 hθ1 hf.ennreal_ofReal hg.ennreal_ofReal
    hh.ennreal_ofReal (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ha,
        ENNReal.ofReal_rpow_of_nonneg (hg0 y) hθ0.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) _)]
      exact ENNReal.ofReal_le_ofReal (hfgh x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ha,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) hθ0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) _)] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)).mp hp

end
end RectangleCLT.Companion.Prekopa

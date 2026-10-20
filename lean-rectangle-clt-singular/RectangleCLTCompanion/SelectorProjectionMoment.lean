import RectangleCLTCompanion.SelectorEntropy
import RectangleCLT.GaussianProjectionMaximum

/-! The actual Gaussian maximum of unit observable rows has a logarithmic
second moment, regardless of rank of the rectangular factor. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

theorem selector_projection_card_bound {p : ℕ} (hp : 1 ≤ p) :
    2 * (p : ℝ) ≤ Real.exp (2 * dimensionLog p) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hc : 2 * (p : ℝ) ≤ Real.exp (dimensionLog p) := by
    rw [dimensionLog, Real.exp_log (mul_pos (Real.exp_pos _) hpR)]
    exact mul_le_mul_of_nonneg_right htwo hpR.le
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  exact hc.trans (Real.exp_le_exp.mpr (by linarith))

theorem selector_projection_max_second_moment
    {p r : ℕ} (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin r) ℝ)
    (hunit : ∀ j, vectorNormSq (A j) = 1) :
    Integrable (fun g => ‖linearProjectionFamily A g‖ ^ 2) (standardGaussian r) ∧
      (∫ g, ‖linearProjectionFamily A g‖ ^ 2 ∂standardGaussian r) ≤
        Real.exp (13 / 2 : ℝ) * dimensionLog p := by
  letI : NeZero p := ⟨by omega⟩
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans hL
  have hA (j : Fin p) : (∑ k, A j k ^ 2) ≤ 1 := by
    simpa only [vectorNormSq] using (hunit j).le
  have hm := projectionMaximum_weighted_moment_le A hA
    (fun g => ‖linearProjectionFamily A g‖) (measurable_linearProjectionFamily A).norm
    (fun g => norm_nonneg _) (d := 1) (L := dimensionLog p) (C := 2)
    (M := Real.sqrt (dimensionLog p)) hL
    (by simpa only [Fintype.card_fin] using selector_projection_card_bound hp)
    (fun g => by simp only [one_mul, le_refl]) le_rfl 2
  have hdom (g : Vector r) : ‖linearProjectionFamily A g‖ ^ 2 ≤
      Real.exp (‖linearProjectionFamily A g‖ / Real.sqrt (dimensionLog p)) *
        (1 + ‖linearProjectionFamily A g‖) ^ 2 := by
    have hR := norm_nonneg (linearProjectionFamily A g)
    have he : 1 ≤ Real.exp (‖linearProjectionFamily A g‖ / Real.sqrt (dimensionLog p)) :=
      Real.one_le_exp_iff.mpr (div_nonneg hR (Real.sqrt_nonneg _))
    calc
      _ ≤ (1 + ‖linearProjectionFamily A g‖) ^ 2 := by nlinarith
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) he
  have hi : Integrable (fun g => ‖linearProjectionFamily A g‖ ^ 2) (standardGaussian r) := by
    apply hm.1.mono' (((measurable_linearProjectionFamily A).norm.pow_const 2).aestronglyMeasurable)
    exact ae_of_all _ fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom g
  refine ⟨hi, ?_⟩
  have hh := (integral_mono hi hm.1 hdom).trans hm.2
  simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, one_mul, Real.sq_sqrt hL0,
    show (2 : ℝ) + (2 + 1) ^ 2 / 2 = 13 / 2 by norm_num, mul_comm] using hh

theorem selector_face_projection_sq_le_max
    {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ) (f : Face p) (g : Vector r) :
    (faceDot (selectorFaceNormal A f) g) ^ 2 ≤ ‖linearProjectionFamily A g‖ ^ 2 := by
  have heq : (faceDot (selectorFaceNormal A f) g) ^ 2 =
      (linearProjectionFamily A g f.1) ^ 2 := by
    unfold faceDot selectorFaceNormal linearProjectionFamily
    cases hf : f.2 <;>
      simp only [hf, Bool.false_eq_true, ↓reduceIte, neg_mul, Finset.sum_neg_distrib, neg_sq]
  rw [heq, ← sq_abs (linearProjectionFamily A g f.1)]
  apply pow_le_pow_left₀ (abs_nonneg _) _ 2
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (linearProjectionFamily A g) f.1

theorem selector_family_log_card_le {p k : ℕ} (hp : 1 ≤ p)
    (S : Finset (Fin (k + 1) → Face p)) (hS : S.Nonempty) :
    Real.log (S.card : ℝ) ≤ 2 * (k + 1 : ℝ) * dimensionLog p := by
  have hc : S.card ≤ (2 * p) ^ (k + 1) := by
    simpa only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.mul_comm] using Finset.card_le_univ S
  have hcR : (S.card : ℝ) ≤ (2 * (p : ℝ)) ^ (k + 1) := by exact_mod_cast hc
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (p : ℝ))
    (selector_projection_card_bound hp) (k + 1)
  have heq : Real.exp (2 * dimensionLog p) ^ (k + 1) =
      Real.exp (2 * (k + 1 : ℝ) * dimensionLog p) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hh := Real.log_le_log (by exact_mod_cast hS.card_pos : 0 < (S.card : ℝ))
    (hcR.trans (hpow.trans_eq heq))
  simpa only [Real.log_exp] using hh

end
end RectangleCLT.Companion

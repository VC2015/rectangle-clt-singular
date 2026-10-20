import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linarith
import RectangleCLT.GaussianFaces

/-! The scalar Laplace integral arising from active exponential thresholds. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace RectangleCLT

theorem integral_natPow_mul_exp_neg_mul_Ioi (q : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Set.Ioi 0, t ^ q * Real.exp (-(r * t))) =
      (q.factorial : ℝ) / r ^ (q + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (q : ℝ) + 1) (by positivity) hr
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [h, Real.rpow_add_one (by positivity), Real.rpow_natCast]
  simp only [one_div_pow, pow_succ, one_div, div_eq_mul_inv]
  ring

theorem integral_natPow_mul_exp_neg_one_add_Ioi (q : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ in Set.Ioi 0, t ^ q * Real.exp (-((1 + T) * t))) =
      (q.factorial : ℝ) / (1 + T) ^ (q + 1) :=
  integral_natPow_mul_exp_neg_mul_Ioi q (by linarith)

theorem integrableOn_natPow_mul_exp_neg_mul_Ioi (q : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ q * Real.exp (-(r * t))) (Set.Ioi 0) := by
  by_contra hn
  have hz := integral_undef hn
  rw [integral_natPow_mul_exp_neg_mul_Ioi q hr] at hz
  have hpos : 0 < (q.factorial : ℝ) / r ^ (q + 1) :=
    div_pos (by exact_mod_cast Nat.factorial_pos q) (pow_pos hr _)
  exact hpos.ne' hz

/-- Integrating the active exponential-density factors gives exactly the
positive soft-face weight, with the factorial from the common exponential
clock. This is an identity of ordinary Lebesgue integrals. -/
theorem integral_active_exponential_kernel {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) :
    (∫ r : ℝ in Set.Ioi 0,
      (∏ f ∈ S, r * w.weight f) * Real.exp (-((1 + w.T) * r))) =
      (S.card.factorial : ℝ) * (w.F * ∏ f ∈ S, w.pi f) := by
  have hr : 0 < 1 + w.T := w.denominator_pos
  calc
    _ = (∏ f ∈ S, w.weight f) *
        (∫ r : ℝ in Set.Ioi 0, r ^ S.card * Real.exp (-((1 + w.T) * r))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun r => by
        simp only [Finset.prod_mul_distrib, Finset.prod_const]
        ring)
    _ = _ := by
      rw [integral_natPow_mul_exp_neg_mul_Ioi _ hr]
      simp only [FaceWeights.F, FaceWeights.pi, Finset.prod_div_distrib,
        Finset.prod_const]
      field_simp [hr.ne']
      ring

theorem integrableOn_active_exponential_kernel {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) :
    IntegrableOn (fun r : ℝ => (∏ f ∈ S, r * w.weight f) *
      Real.exp (-((1 + w.T) * r))) (Set.Ioi 0) := by
  have hi := (integrableOn_natPow_mul_exp_neg_mul_Ioi S.card w.denominator_pos).const_mul
    (∏ f ∈ S, w.weight f)
  apply hi.congr
  exact ae_of_all _ (fun r => by
    simp only [Finset.prod_mul_distrib, Finset.prod_const]
    ring)

theorem lintegral_active_exponential_kernel {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) :
    (∫⁻ r : ℝ in Set.Ioi 0, ENNReal.ofReal
      ((∏ f ∈ S, r * w.weight f) * Real.exp (-((1 + w.T) * r)))) =
      ENNReal.ofReal ((S.card.factorial : ℝ) * (w.F * ∏ f ∈ S, w.pi f)) := by
  rw [← integral_active_exponential_kernel w S]
  symm
  apply ofReal_integral_eq_lintegral_ofReal (integrableOn_active_exponential_kernel w S)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact mul_nonneg
    (Finset.prod_nonneg (fun f _ => mul_nonneg (le_of_lt hr) (w.nonneg f)))
    (Real.exp_pos _).le

end RectangleCLT

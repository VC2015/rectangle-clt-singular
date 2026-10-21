import RectangleCLTCompanion.SubexponentialArray
import RectangleCLTCompanion.SubexponentialScales
import RectangleCLTCompanion.SubexponentialResidualMGF

/-! Probability coupling for the normalized clipped residual array. -/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace RectangleCLT.Companion
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Normalized residual coupling at an arbitrary nonnegative cutoff. -/
theorem normalized_exp_residual_tail {n p : ℕ} (hn : 1 ≤ n)
    {X : Fin n → Ω → Vector p} {K u s : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    μ.real {ω | K * (s + 4 * (n : ℝ) * Real.exp (-u)) / Real.sqrt (n : ℝ) <
      ‖sumVector (normalizedResidualRows μ X (K * u)) ω‖} ≤
      (p : ℝ) * Real.exp (-s) := by
  classical
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one h.one_le_scale
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hv : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  let r := K * (s + 4 * (n : ℝ) * Real.exp (-u)) / Real.sqrt (n : ℝ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hscale : K * (s + 4 * (n : ℝ) * Real.exp (-u)) = Real.sqrt (n : ℝ) * r := by
    dsimp only [r]
    field_simp [hv.ne']
  have hsub : {ω | r < ‖sumVector (normalizedResidualRows μ X (K * u)) ω‖} ⊆
      {ω | ∃ j : Fin p, K * (s + 4 * (n : ℝ) * Real.exp (-u)) ≤
        |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} := by
    intro ω hω
    have hexists : ∃ j : Fin p, r < ‖sumVector (normalizedResidualRows μ X (K * u)) ω j‖ := by
      by_contra hnex
      have hcoord : ∀ j : Fin p, ‖sumVector (normalizedResidualRows μ X (K * u)) ω j‖ ≤ r := by
        intro j
        exact le_of_not_gt (fun hj => hnex ⟨j, hj⟩)
      exact (not_le_of_gt hω) ((pi_norm_le_iff_of_nonneg hr).mpr hcoord)
    obtain ⟨j, hj⟩ := hexists
    refine ⟨j, ?_⟩
    have heq : sumVector (normalizedResidualRows μ X (K * u)) ω j =
        (Real.sqrt (n : ℝ))⁻¹ * ∑ i, centeredClipResidual μ (fun a => X i a j) K u ω := by
      simp only [sumVector, normalizedResidualRows, centeredResidualRows,
        centeredClipResidual, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr hv.le)] at hj
    rw [hscale]
    have hh := mul_lt_mul_of_pos_left hj hv
    simpa only [← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul] using hh.le
  exact (measureReal_mono hsub).trans
    (residual_array_tail X hK (fun i j => h.coordinate_exponentialMomentBound i j) h.independent hu)

/-- The cutoff used in the corollary makes the total residual mean negligible. -/
private theorem four_n_tail_le_one {n : ℕ} (hn : 1 ≤ n) :
    4 * (n : ℝ) * Real.exp (-(4 * dimensionLog n)) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  let f := subexponentialTailFactor n
  have hf : 0 ≤ f := subexponentialTailFactor_nonneg n
  have ht : f ≤ 1 / (2 * (n : ℝ)) := subexponentialTailFactor_le_inv_two_mul hn
  have ht' : 2 * (n : ℝ) * f ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 2 * (n : ℝ) by positivity)).mp ht
    nlinarith
  have hfhalf : 2 * f ≤ 1 := by
    have hh := mul_nonneg (sub_nonneg.mpr hnR) hf
    nlinarith
  have hsq := mul_le_mul_of_nonneg_right ht' (show 0 ≤ 2 * f by positivity)
  have hexp : Real.exp (-(4 * dimensionLog n)) = f ^ 2 := by
    dsimp only [f, subexponentialTailFactor]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  nlinarith

/-- Ready-to-use row residual coupling with the manuscript's original radius. -/
theorem normalized_residual_tail_log {n p : ℕ} {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    μ.real {ω | subexponentialResidualRadius n p K <
      ‖sumVector (normalizedResidualRows μ X (K * (4 * dimensionLog n))) ω‖} ≤
      1 / (2 * (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  have hppos : 0 < (p : ℝ) := zero_lt_one.trans_le hpR
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one h.one_le_scale
  let s := subexponentialUnionLog n p
  have hs : 0 ≤ s := (subexponentialUnionLog_pos hn hp).le
  have hf : 0 ≤ subexponentialTailFactor n := subexponentialTailFactor_nonneg n
  have hslo : (3 / 4 : ℝ) ≤ s := by
    have hnp : (1 : ℝ) ≤ (n : ℝ) * (p : ℝ) := one_le_mul_of_one_le_of_one_le hnR hpR
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (show (4 : ℝ) ≤ 4 * (n : ℝ) * (p : ℝ) by nlinarith)
    have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hlo
    exact hlo.trans hlog
  have hu : 0 ≤ 4 * dimensionLog n := by
    have hh : 1 ≤ dimensionLog n := log_exp_mul_nat_ge_one hn
    exact mul_nonneg (by norm_num) (zero_le_one.trans hh)
  have hsmall := four_n_tail_le_one hn
  have hnum : s + 4 * (n : ℝ) * Real.exp (-(4 * dimensionLog n)) ≤ 4 * s := by linarith
  have hrad : K * (s + 4 * (n : ℝ) * Real.exp (-(4 * dimensionLog n))) /
      Real.sqrt (n : ℝ) ≤ subexponentialResidualRadius n p K := by
    calc
      _ ≤ 4 * K * s / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hnum hK.le])
          (Real.sqrt_nonneg _)
      _ ≤ _ := by
        unfold subexponentialResidualRadius
        dsimp only [s]
        exact le_add_of_nonneg_left (by positivity)
  have ht := normalized_exp_residual_tail hn h hu hs
  have hsub : {ω | subexponentialResidualRadius n p K <
      ‖sumVector (normalizedResidualRows μ X (K * (4 * dimensionLog n))) ω‖} ⊆
      {ω | K * (s + 4 * (n : ℝ) * Real.exp (-(4 * dimensionLog n))) /
        Real.sqrt (n : ℝ) <
        ‖sumVector (normalizedResidualRows μ X (K * (4 * dimensionLog n))) ω‖} := by
    intro ω hω
    exact lt_of_le_of_lt hrad hω
  apply (measureReal_mono hsub).trans (ht.trans _)
  have heq : (p : ℝ) * Real.exp (-s) = 1 / (4 * (n : ℝ)) := by
    dsimp only [s, subexponentialUnionLog]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp [hnpos.ne', hppos.ne'] <;> ring
  rw [heq]
  exact one_div_le_one_div_of_le (show 0 < 2 * (n : ℝ) by positivity) (by nlinarith)

end
end RectangleCLT.Companion

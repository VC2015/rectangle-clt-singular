import RectangleCLTCompanion.SubexponentialArray
import RectangleCLTCompanion.SubexponentialScales

/-! Exponentially rare clipping residuals are controlled by a positive-sum
Laplace bound. The cutoff is large enough that their absolute means can be
paid directly, avoiding any separate Bernstein theorem. -/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def centeredClipResidual (μ : Measure Ω) (X : Ω → ℝ) (K u : ℝ) : Ω → ℝ :=
  fun ω => clipResidual (K * u) (X ω) - ∫ a, clipResidual (K * u) (X a) ∂μ

/-- The exponential moment of the actual sum of absolute residuals. -/
theorem absolute_residual_sum_mgf_le {n : ℕ} (X : Fin n → Ω → ℝ) {K u : ℝ}
    (hX : ∀ i, ExponentialMomentBound μ (X i) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) :
    Integrable (fun ω => Real.exp ((1 / K) * ∑ i, |clipResidual (K * u) (X i ω)|)) μ ∧
    mgf (fun ω => ∑ i, |clipResidual (K * u) (X i ω)|) μ (1 / K) ≤
      Real.exp (2 * (n : ℝ) * Real.exp (-u)) := by
  let Y : Fin n → Ω → ℝ := fun i ω => |clipResidual (K * u) (X i ω)|
  have hmeas : ∀ i, Measurable (Y i) := fun i =>
    ((clipResidual_continuous _).measurable.comp (hX i).measurable).abs
  have hi : iIndepFun Y μ :=
    hind.comp (fun _ x => |clipResidual (K * u) x|)
      (fun _ => (clipResidual_continuous _).measurable.abs)
  have hint (i : Fin n) : Integrable (fun ω => Real.exp ((1 / K) * Y i ω)) μ := by
    simpa only [Y, one_div_mul_eq_div] using (hX i).integrable_exp_abs_residual hu
  have hsum := hi.integrable_exp_mul_sum hmeas (s := Finset.univ) (fun i _ => hint i)
  refine ⟨?_, ?_⟩
  · simpa only [Finset.sum_apply] using hsum
  · have heq : (fun ω => ∑ i, |clipResidual (K * u) (X i ω)|) =
        ∑ i ∈ (Finset.univ : Finset (Fin n)), Y i := by ext ω; simp [Y]
    rw [heq, hi.mgf_sum hmeas Finset.univ]
    calc
      _ ≤ ∏ _i : Fin n, Real.exp (2 * Real.exp (-u)) := by
        apply Finset.prod_le_prod (fun _ _ => mgf_nonneg)
        intro i _
        have hm : mgf (Y i) μ (1 / K) ≤ 1 + 2 * Real.exp (-u) := by
          simpa only [mgf, Y, one_div_mul_eq_div] using (hX i).integral_exp_abs_residual_le hu
        exact hm.trans (by linarith [Real.add_one_le_exp (2 * Real.exp (-u))])
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
        congr 1
        ring

/-- A direct scalar residual tail with its absolute-mean cost explicit. -/
theorem residual_sum_abs_tail {n : ℕ} (X : Fin n → Ω → ℝ) {K u s : ℝ}
    (hK : 0 < K) (hX : ∀ i, ExponentialMomentBound μ (X i) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) :
    μ.real {ω | K * (s + 4 * (n : ℝ) * Real.exp (-u)) ≤
      |∑ i, centeredClipResidual μ (X i) K u ω|} ≤ Real.exp (-s) := by
  let S : Ω → ℝ := fun ω => ∑ i, |clipResidual (K * u) (X i ω)|
  have hm (i : Fin n) : |∫ a, clipResidual (K * u) (X i a) ∂μ| ≤ 2 * K * Real.exp (-u) := by
    have hh := norm_integral_le_integral_norm (μ := μ) (fun a => clipResidual (K * u) (X i a))
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans ((hX i).integral_abs_residual_le hu)
  have hmean : (∑ i, |∫ a, clipResidual (K * u) (X i a) ∂μ|) ≤
      2 * (n : ℝ) * K * Real.exp (-u) := by
    exact (Finset.sum_le_sum (fun i _ => hm i)).trans_eq (by simp; ring)
  have hcenter (ω : Ω) : |∑ i, centeredClipResidual μ (X i) K u ω| ≤
      S ω + 2 * (n : ℝ) * K * Real.exp (-u) := by
    simp only [centeredClipResidual, Finset.sum_sub_distrib]
    have h₁ := Finset.abs_sum_le_sum_abs (fun i : Fin n => clipResidual (K * u) (X i ω)) Finset.univ
    have h₂ := Finset.abs_sum_le_sum_abs (fun i : Fin n => ∫ a, clipResidual (K * u) (X i a) ∂μ) Finset.univ
    exact (abs_sub _ _).trans (add_le_add h₁ (h₂.trans hmean))
  have hsub : {ω | K * (s + 4 * (n : ℝ) * Real.exp (-u)) ≤
      |∑ i, centeredClipResidual μ (X i) K u ω|} ⊆
      {ω | K * (s + 2 * (n : ℝ) * Real.exp (-u)) ≤ S ω} := by
    intro ω hω
    have hh := hcenter ω
    dsimp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith
  have hbound := absolute_residual_sum_mgf_le X hX hind hu
  have hchernoff := measure_ge_le_exp_mul_mgf (X := S) (t := 1 / K)
    (K * (s + 2 * (n : ℝ) * Real.exp (-u))) (by positivity) hbound.1
  apply (measureReal_mono hsub).trans (hchernoff.trans _)
  calc
    _ ≤ Real.exp (-(1 / K) * (K * (s + 2 * (n : ℝ) * Real.exp (-u)))) *
        Real.exp (2 * (n : ℝ) * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hbound.2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp [hK.ne'] <;> ring

/-- A union bound preserves arbitrary dependence within each row. -/
theorem residual_array_tail {n p : ℕ} (X : Fin n → Ω → Fin p → ℝ) {K u s : ℝ}
    (hK : 0 < K) (hX : ∀ i j, ExponentialMomentBound μ (fun ω => X i ω j) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) :
    μ.real {ω | ∃ j : Fin p, K * (s + 4 * (n : ℝ) * Real.exp (-u)) ≤
      |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} ≤
      (p : ℝ) * Real.exp (-s) := by
  let r := K * (s + 4 * (n : ℝ) * Real.exp (-u))
  have htail (j : Fin p) :
      μ.real {ω | r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} ≤ Real.exp (-s) :=
    residual_sum_abs_tail (fun i ω => X i ω j) hK (fun i => hX i j)
      (hind.comp (fun _ x => x j) (fun _ => measurable_pi_apply j)) hu
  have heq : {ω | ∃ j : Fin p, r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} =
      ⋃ j : Fin p, {ω | r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} := by ext ω; simp
  rw [heq]
  calc
    _ ≤ ∑ j : Fin p, μ.real {ω | r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin p, Real.exp (-s) := Finset.sum_le_sum (fun j _ => htail j)
    _ = _ := by simp

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
    have hh := log_exp_mul_nat_ge_one hn
    linarith
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
    field_simp [hnpos.ne', hppos.ne']
  rw [heq]
  exact one_div_le_one_div_of_le (show 0 < 2 * (n : ℝ) by positivity) (by nlinarith)

end
end RectangleCLT.Companion

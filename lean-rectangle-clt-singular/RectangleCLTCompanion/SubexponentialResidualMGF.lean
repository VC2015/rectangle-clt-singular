import RectangleCLTCompanion.SubexponentialClipping
import Mathlib.Probability.Moments.Basic

/-! Direct Laplace control of sums of absolute clipping residuals. -/

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
    continuous_abs.measurable.comp ((clipResidual_continuous _).measurable.comp (hX i).measurable)
  have hi : iIndepFun Y μ :=
    hind.comp (fun _ x => |clipResidual (K * u) x|)
      (fun _ => continuous_abs.measurable.comp (clipResidual_continuous _).measurable)
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
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp [hK.ne']; ring

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

end
end RectangleCLT.Companion

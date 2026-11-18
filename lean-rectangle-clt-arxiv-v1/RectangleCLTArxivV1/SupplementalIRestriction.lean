import RectangleCLTArxivV1.SupplementalGSeededBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The exceptional-gap reduction restricts only the first two selector
indices. The smoother and all remaining logistic factors are unchanged. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def exceptionalCutoffDet (c : ℝ) : ℝ := c*(2-c)

def correlationAngleWeight (ρ : ℝ) : ℝ := Real.arccos ρ*Real.sqrt (1-ρ^2)

def separatedFirstPair {p r K : ℕ} (U : Face p → Vector r) (c : ℝ)
    (α : Fin (K+2) → Face p) : Prop := c ≤ 1-|faceDot (U (α 0)) (U (α 1))|

def separatedSelectorTuples {p r : ℕ} (U : Face p → Vector r) (c : ℝ) (K : ℕ) :
    Finset (Fin (K+2) → Face p) := by
  classical
  exact Finset.univ.filter (separatedFirstPair U c)

theorem exceptionalCutoffDet_bounds {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 < exceptionalCutoffDet c ∧ c ≤ exceptionalCutoffDet c ∧ exceptionalCutoffDet c ≤ 1 := by
  unfold exceptionalCutoffDet
  have hprod := mul_nonneg hc.le (show 0 ≤ 1-c by linarith)
  constructor
  · exact mul_pos hc (by linarith)
  · constructor <;> nlinarith [sq_nonneg (1-c)]

theorem correlationAngleWeight_nonneg (ρ : ℝ) : 0 ≤ correlationAngleWeight ρ :=
  mul_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _)

theorem correlationAngleWeight_ge_det (ρ : ℝ) : 1-ρ^2 ≤ correlationAngleWeight ρ := by
  by_cases hd : 0 ≤ 1-ρ^2
  · have hs := mul_le_mul_of_nonneg_right (Real.sin_le (Real.arccos_nonneg ρ)) (Real.sqrt_nonneg (1-ρ^2))
    rw [Real.sin_arccos] at hs
    simpa only [← pow_two,Real.sq_sqrt hd] using hs
  · exact (le_of_not_ge hd).trans (correlationAngleWeight_nonneg ρ)

theorem exceptionalCutoffDet_le_angle {c ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hsep : c ≤ 1-|ρ|) : exceptionalCutoffDet c ≤ correlationAngleWeight ρ := by
  have hgap : exceptionalCutoffDet c ≤ 1-ρ^2 := by
    unfold exceptionalCutoffDet
    have hp := mul_nonneg (show 0 ≤ 1-c-|ρ| by linarith) (show 0 ≤ 1-c+|ρ| by linarith [abs_nonneg ρ])
    nlinarith [sq_abs ρ]
  exact hgap.trans (correlationAngleWeight_ge_det ρ)

/-- Appending restoration factors preserves the first-pair restriction as
soon as the first two indices are retained. No other index is restricted. -/
theorem separatedFirstPair_congr {p r K N : ℕ} (U : Face p → Vector r) (c : ℝ)
    (α : Fin (K+2) → Face p) (β : Fin (N+2) → Face p)
    (h0 : β 0=α 0) (h1 : β 1=α 1) : separatedFirstPair U c β ↔ separatedFirstPair U c α := by
  unfold separatedFirstPair
  rw [h0,h1]

/-- The finite nonnegative reduction before using any hard-facet/matrix
estimate. In particular it applies to every restoration tuple length. -/
theorem separated_nonnegative_sum_le_angle_weighted
    {p r K : ℕ} (U : Face p → Vector r) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (N : (Fin (K+2) → Face p) → ℝ) (hN : ∀ α, 0 ≤ N α) :
    exceptionalCutoffDet c*(∑ α ∈ separatedSelectorTuples U c K, N α) ≤
      ∑ α, correlationAngleWeight (faceDot (U (α 0)) (U (α 1)))*N α := by
  classical
  rw [separatedSelectorTuples,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  by_cases hsep : separatedFirstPair U c α
  · rw [if_pos hsep]
    exact mul_le_mul_of_nonneg_right (exceptionalCutoffDet_le_angle hc hc1 hsep) (hN α)
  · rw [if_neg hsep,mul_zero]
    exact mul_nonneg (correlationAngleWeight_nonneg _) (hN α)

/-- Actual selector-score matrices satisfy the restricted comparison. This
has no assumed nuclear-sum bound: its right side is the full actual
angle-weighted matrix sum to which AppendixH applies. -/
theorem separated_selector_nuclear_integral_le_angle_weighted
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (U : Face p → Vector r) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ ω, ∑ α ∈ separatedSelectorTuples U c K,
      symmetricNuclearNorm (selectorGaussianScore s A V α ω) ∂μ) ≤
      (∫ ω, ∑ α : Fin (K+2) → Face p,
        correlationAngleWeight (faceDot (U (α 0)) (U (α 1)))*
          symmetricNuclearNorm (selectorGaussianScore s A V α ω) ∂μ)/exceptionalCutoffDet c := by
  classical
  let N := fun (α : Fin (K+2) → Face p) (ω : Ω) =>
    symmetricNuclearNorm (selectorGaussianScore s A V α ω)
  have hsum := integrable_selector_nuclear_sum (k := K+2) μ s A V hV
  have hi (α : Fin (K+2) → Face p) : Integrable (N α) μ := by
    apply hsum.mono' (measurable_selectorGaussianScore_nuclear s A V hV α).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      change ‖symmetricNuclearNorm (selectorGaussianScore s A V α ω)‖ ≤
        ∑ β : Fin (K+2) → Face p, symmetricNuclearNorm (selectorGaussianScore s A V β ω)
      rw [Real.norm_eq_abs,abs_of_nonneg (symmetricNuclearNorm_nonneg _)]
      exact Finset.single_le_sum (fun (β : Fin (K+2) → Face p) _ =>
        symmetricNuclearNorm_nonneg (selectorGaussianScore s A V β ω)) (Finset.mem_univ α))
  have hri : Integrable (fun ω => ∑ α ∈ separatedSelectorTuples U c K, N α ω) μ :=
    integrable_finset_sum _ (fun α _ => hi α)
  have hwi : Integrable (fun ω => ∑ α : Fin (K+2) → Face p,
      correlationAngleWeight (faceDot (U (α 0)) (U (α 1)))*N α ω) μ :=
    integrable_finset_sum _ (fun α _ => (hi α).const_mul _)
  have ht := integral_mono (hri.const_mul (exceptionalCutoffDet c)) hwi
    (fun ω => separated_nonnegative_sum_le_angle_weighted U hc hc1 (fun α => N α ω)
      (fun α => symmetricNuclearNorm_nonneg _))
  rw [integral_const_mul] at ht
  exact (le_div_iff₀ (exceptionalCutoffDet_bounds hc hc1).1).mpr (by simpa only [mul_comm] using ht)

end
end RectangleCLTArxivV1

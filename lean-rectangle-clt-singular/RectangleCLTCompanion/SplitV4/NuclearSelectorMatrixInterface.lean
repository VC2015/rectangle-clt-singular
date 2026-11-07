import RectangleCLTCompanion.SplitV4.LogisticSelectorMatrixBound

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem averagedSelectorMatrixEstimate_of_nuclear_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν] (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V) (K T : ℝ)
    (hnuc : ∀ q : ℕ, 1 ≤ q → (∫ ω, ∑ α : Fin q → Face p,
      symmetricNuclearNorm (selectorGaussianScore s A V α ω) ∂ν) ≤ K ^ (q + 1) * T) :
    AveragedSelectorMatrixEstimate s ν A V K T := by
  intro q hq b hb B hBm hB
  have hMeas (α : Fin q → Face p) : Measurable (fun ω =>
      Matrix.trace (B α ω * selectorGaussianScore s A V α ω)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro l _
    exact (hBm α j l).mul (measurable_selectorGaussianScore_entry s A V hV α l j)
  have hpoint (ω : Ω) : (∑ α : Fin q → Face p,
      |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)|) ≤
        b * ∑ α : Fin q → Face p, symmetricNuclearNorm (selectorGaussianScore s A V α ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    exact abs_trace_mul_le_nuclear_of_quadratic (B α ω) _
      (selectorGaussianScore_isHermitian s A V α ω) (hB α ω)
  have hi : Integrable (fun ω => ∑ α : Fin q → Face p,
      |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)|) ν := by
    apply ((integrable_selector_nuclear_sum ν s A V hV).const_mul b).mono'
      (Finset.measurable_sum _ (fun α _ => (hMeas α).abs)).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun α _ => abs_nonneg _))]
      exact hpoint ω)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, b * ∑ α : Fin q → Face p,
        symmetricNuclearNorm (selectorGaussianScore s A V α ω) ∂ν :=
      integral_mono hi ((integrable_selector_nuclear_sum ν s A V hV).const_mul b) hpoint
    _ = b * ∫ ω, ∑ α : Fin q → Face p,
        symmetricNuclearNorm (selectorGaussianScore s A V α ω) ∂ν := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hnuc q hq) hb

theorem averagedSelectorMatrixEstimate_of_rectangle_concentration
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} (hp : 1 ≤ p)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (hA : ∀ j, vectorNormSq (A j) = 1)
    {C δ σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hδh : δ ≤ s.bandwidth) (hσ : 0 ≤ σ)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hc : RectangleBaseConcentration (ν.map V) C δ (dimensionLog p)) :
    AveragedSelectorMatrixEstimate s ν (σ • A) V logisticMatrixConstant
      (C * (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))) := by
  letI : IsProbabilityMeasure (ν.map V) := isProbabilityMeasure_map hV.aemeasurable
  apply averagedSelectorMatrixEstimate_of_nuclear_bound ν s (σ • A) V hV
  intro q hq
  have hn := selector_nuclear_bound_of_rectangle_concentration hp (ν.map V) s A hA hC hδ hδh hσ hscale hc q hq
  have hm : AEStronglyMeasurable (fun v : Vector p => ∑ α : Fin q → Face p,
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) id α v)) (ν.map V) :=
    (integrable_selector_nuclear_sum (ν.map V) s (σ • A) id measurable_id).aestronglyMeasurable
  rw [integral_map hV.aemeasurable hm] at hn
  simpa only [selectorGaussianScore, id_eq, mul_assoc] using hn

end

end RectangleCLT.Companion.SplitV4

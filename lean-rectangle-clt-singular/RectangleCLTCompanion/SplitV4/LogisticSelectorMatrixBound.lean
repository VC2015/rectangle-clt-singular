import RectangleCLTCompanion.SplitV4.LogisticActiveConcentration

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem selectorGaussianScore_zero_factor {p r k : ℕ} (s : FaceSmoother p)
    (V : Vector p) (α : Fin k → Face p) :
    selectorGaussianScore s (0 : Matrix (Fin p) (Fin r) ℝ) id α V = 0 := by
  unfold selectorGaussianScore
  simp only [Matrix.zero_mulVec, zero_add, id_eq]
  exact weightedScore_standardGaussian_const r _

theorem selector_nuclear_bound_of_rectangle_concentration {p r : ℕ} (hp : 1 ≤ p)
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (hA : ∀ j, vectorNormSq (A j) = 1)
    {C δ σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hδh : δ ≤ s.bandwidth) (hσ : 0 ≤ σ)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hc : RectangleBaseConcentration μ C δ (dimensionLog p)) (k : ℕ) (hk : 1 ≤ k) :
    (∫ v, ∑ α : Fin k → Face p,
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) id α v) ∂μ) ≤
        logisticMatrixConstant ^ (k + 1) * C *
          (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  have hR : 0 ≤ logisticMatrixConstant ^ (k + 1) * C *
      (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
    exact mul_nonneg (mul_nonneg (pow_nonneg logisticMatrixConstant_pos.le _) hC.le)
      (mul_nonneg (mul_nonneg s.bandwidth_pos.le
        (zero_le_one.trans (log_exp_mul_nat_ge_one hp))) (Real.sqrt_nonneg _))
  by_cases hσ0 : σ = 0
  · subst σ
    simpa only [zero_smul, selectorGaussianScore_zero_factor, symmetricNuclearNorm_zero,
      Finset.sum_const_zero, integral_zero] using hR
  have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
  by_cases hm0 : s.faces.card = 0
  · have hs0 : s.faces = ∅ := Finset.card_eq_zero.mp hm0
    have hz (α : Fin k → Face p) (v : Vector p) : selectorGaussianScore s (σ • A) id α v = 0 := by
      apply selectorGaussianScore_inactive
      intro ha
      have hi : (0 : ℕ) < k := by omega
      have hh := ha ⟨0, hi⟩
      simpa only [hs0, Finset.not_mem_empty] using hh
    simpa only [hz, symmetricNuclearNorm_zero, Finset.sum_const_zero, integral_zero] using hR
  have hm : 1 ≤ s.faces.card := by omega
  let P := μ.map (activeFaceProjection s)
  letI : IsProbabilityMeasure P := isProbabilityMeasure_map (measurable_activeFaceProjection s).aemeasurable
  have hcard : s.faces.card ≤ 2 * p := by
    have hh := Finset.card_le_card (s.faces.subset_univ)
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm] using hh
  have ht : TransitionMassBound P id s.bandwidth
      (4 * C * s.bandwidth * Real.sqrt (dimensionLog p)) := by
    intro t ht z
    exact (hc.active_transitionMassBound s s.bandwidth_pos t ht z).trans
      (transition_budget_le_four hC.le hδh s.bandwidth_pos.le)
  have hn := projected_logistic_matrix_bound hm P (activeFaceNormals s A) (activeFaceOffsets s)
    (activeFaceNormals_unit s A hA) hC hδ s.bandwidth_pos hσp
    (threshold_dimensionLog_faces_le hm hp hcard) hscale
    (hc.active_coordinate_concentration s) ht k hk
  have hmP : AEStronglyMeasurable (fun y : Vector s.faces.card => ∑ α : Fin k → Fin s.faces.card,
      symmetricNuclearNorm (projectedLogisticGaussianScore (activeFaceNormals s A)
        (activeFaceOffsets s) s.bandwidth s.bandwidth_pos σ α y)) P :=
    (integrable_projectedLogistic_nuclear_sum P _ _ s.bandwidth_pos σ).aestronglyMeasurable
  rw [integral_map (measurable_activeFaceProjection s).aemeasurable hmP] at hn
  simpa only [sum_selector_nuclear_eq_active] using hn

end

end RectangleCLT.Companion.SplitV4

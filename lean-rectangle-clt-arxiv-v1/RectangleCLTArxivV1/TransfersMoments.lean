import RectangleCLTArxivV1.TransfersStatements
import RectangleCLTCompanion.SplitV4.ConditionalPolynomial

/-! Actual second moments, covariance factors and marginal-law inputs for
Theorem 2(i). No coordinate fourth-moment condition is used. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
  RectangleCLT.Companion.SplitV4
open scoped BigOperators

namespace PolynomialEnvelopeHypotheses
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {X : Fin n → Ω → Vector p} {q B : ℝ}

/-- The envelope class alone supplies all genuine coordinate second moments. -/
theorem coordinate_memLp_two (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 2 < q) (i : Fin n) (j : Fin p) :
    MemLp (fun ω => X i ω j) 2 μ := by
  have hsq : Integrable (fun ω => ‖X i ω‖ ^ 2) μ := by
    apply ((integrable_const (1 : ℝ)).add (h.envelope_integrable i)).mono'
      ((h.measurable i).norm.pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro ω
    simpa only [Real.norm_eq_abs, abs_sq] using
      norm_pow_two_le_one_add_rpow (X i ω) hq.le
  apply (memLp_two_iff_integrable_sq
    ((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable).mpr
  apply hsq.mono' (((measurable_pi_apply j).comp (h.measurable i)).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_sq]
  have hh := norm_le_pi_norm (X i ω) j
  simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg (X i ω j)) hh 2

/-- Actual covariance factors exist in the envelope-only class, even when
`2<q<4`; no fourth moment is introduced for this purpose. -/
theorem gaussian_factor_exists (h : PolynomialEnvelopeHypotheses μ X q B) (hq : 2 < q) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (normalizedObservationSum X) := by
  obtain ⟨A, hA⟩ := normalizedSummands_gaussian_factor_exists
    (h.coordinate_memLp_two hq) h.centered
  exact ⟨A, by simpa only [sumVector_normalizedSummands] using hA⟩

/-- The printed average marginal normalization is exactly the covariance
normalization of the actual normalized sum. -/
theorem unit_covariance (h : PolynomialEnvelopeHypotheses μ X q B) (hq : 2 < q) (j : Fin p) :
    covariance μ (normalizedObservationSum X) j j = 1 := by
  have hh := normalizedSummands_unit_covariance h.independent (h.coordinate_memLp_two hq)
    h.centered h.average_second j
  simpa only [sumVector_normalizedSummands] using hh

/-- The actual marginal laws, with no supplied distribution-construction
premise, meet the conditional truncation contract at every allowed cutoff. -/
theorem conditional_marginal_inputs (h : PolynomialEnvelopeHypotheses μ X q B)
    (hq : 2 < q) (hB : 1 ≤ B) {T : ℝ} (hT : 2 * B ≤ T) (i : Fin n) :
    ConditionalTruncationMomentHypotheses (μ.map (X i)) B T q :=
  conditionalTruncationMomentHypotheses_marginal μ X h.measurable hB hT hq
    h.envelope_integrable h.envelope_moment h.centered i

/-- The reference average covariance in the conditional-law construction
is the actual covariance of the original normalized independent sum. -/
theorem covariance_eq_originalAverageCovariance
    (h : PolynomialEnvelopeHypotheses μ X q B) (hq : 2 < q) (hB : 1 ≤ B) (hn : 1 ≤ n) :
    covariance μ (normalizedObservationSum X) =
      originalAverageCovariance (fun i => μ.map (X i)) := by
  let ν : Fin n → Measure (Vector p) := fun i => μ.map (X i)
  haveI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (h.measurable i).aemeasurable
  have hm := h.conditional_marginal_inputs hq hB (le_refl (2 * B))
  have htuple : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ h.measurable
  have hmap : μ.map (fun ω i => X i ω) = Measure.pi ν :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (h.measurable i).aemeasurable)).mp h.independent
  let W := normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)
  have hW : Measurable W := by
    unfold W normalizedObservationSum sumVector
    exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  have hc : covariance (Measure.pi ν) W = covariance μ (normalizedObservationSum X) := by
    rw [← hmap, covariance_map_of_measurable μ _ htuple W hW]
    rfl
  rw [← hc]
  exact product_normalized_covariance_eq_average ν hm hn

end PolynomialEnvelopeHypotheses
end RectangleCLTArxivV1

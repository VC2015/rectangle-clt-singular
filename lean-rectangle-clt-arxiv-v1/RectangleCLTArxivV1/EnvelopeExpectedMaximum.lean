import RectangleCLTCompanion.SplitV4.Printed.EnvelopeMaximum

/-! Lemma E.1 of the frozen arXiv v1 source, with its envelope scale
explicitly nonnegative. Without `A ≥ 0`, the printed real-budget statement
is false: take zero vectors, `q=4`, `v=0`, and `A=-1`. Genuine finite
q-moments supply the second-moment integrability used by the proved archive
Bernstein and layer-cake argument. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
universe u

/-- The printed real-budget formula cannot hold with a negative scale,
even for zero observations and a positive proposed coefficient. -/
theorem expectedMaximum_negative_budget_obstruction {C : ℝ} (hC : 0 < C) :
    ¬ (0 ≤ C*(Real.sqrt (0*dimensionLog 1)+
      (-1)*dimensionLog 1^(1-1/(4:ℝ)))) := by
  simp only [dimensionLog,Nat.cast_one,mul_one,Real.log_exp,zero_mul,Real.sqrt_zero,
    Real.one_rpow,mul_one,zero_add,mul_neg_one]
  linarith

/-- Genuine finite q-envelope moments imply all coordinate second moments. -/
theorem coordinate_sq_integrable_of_envelope_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} (Y : Ω → Vector p) (hY : Measurable Y) {q : ℝ}
    (hq : 2 ≤ q) (hmoment : Integrable (fun ω => ‖Y ω‖^q) μ) (j : Fin p) :
    Integrable (fun ω => Y ω j^2) μ := by
  have hnorm : Integrable (fun ω => ‖Y ω‖^2) μ := by
    apply ((integrable_const (1:ℝ)).add hmoment).mono'
      (hY.norm.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_pow_two_le_one_add_rpow (Y ω) hq
  apply hnorm.mono' (((measurable_pi_apply j).comp hY).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs,abs_sq]
  have hh := norm_le_pi_norm (Y ω) j
  simpa only [Real.norm_eq_abs,sq_abs] using
    pow_le_pow_left₀ (norm_nonneg (Y ω j)) hh 2

/-- The expected norm below is a genuine finite expectation. -/
theorem integrable_norm_sum_of_envelope_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) {q : ℝ}
    (hq : 2 ≤ q) (hmoment : ∀ i, Integrable (fun ω => ‖Y i ω‖^q) μ) :
    Integrable (fun ω => ‖sumVector Y ω‖) μ := by
  have hi (i : Fin n) : Integrable (fun ω => ‖Y i ω‖) μ := by
    apply ((integrable_const (2:ℝ)).add (hmoment i)).mono' (hY i).norm.aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    change ‖Y i ω‖ ≤ 2+‖Y i ω‖^q
    have hs := norm_pow_two_le_one_add_rpow (Y i ω) hq
    nlinarith [sq_nonneg (‖Y i ω‖-(1/2:ℝ))]
  apply (integrable_finset_sum Finset.univ (fun i _ => hi i)).mono'
    ((Finset.measurable_sum Finset.univ (fun i _ => hY i)).norm.aestronglyMeasurable)
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact norm_sum_le Finset.univ (fun i => Y i ω)

/-- The exact expected-maximum rate, with the necessary nonnegative
budget qualification and no separately assumed second integrability. -/
theorem expected_maximum_under_envelope_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (Y : Fin n → Ω → Vector p) (hp : 1 ≤ p)
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ)=0)
    {q A v : ℝ} (hq : 2 < q) (hA : 0 ≤ A)
    (hmoment : ∀ i, Integrable (fun ω => ‖Y i ω‖^q) μ)
    (hbudget : (∑ i, ∫ ω, ‖Y i ω‖^q ∂μ)≤A^q)
    (hvariance : ∀ j, (∑ i, ∫ ω, Y i ω j^2 ∂μ)≤v) :
    (∫ ω, ‖sumVector Y ω‖ ∂μ) ≤ envelopeMaximumConstant *
      (Real.sqrt (v*dimensionLog p)+A*dimensionLog p^(1-1/q)) := by
  exact Printed.expected_maximum_under_envelope_moment Y hp hY hind hcenter hq hA
    (fun i j => coordinate_sq_integrable_of_envelope_moment (Y i) (hY i) hq.le (hmoment i) j)
    hvariance hmoment hbudget

/-- Corrected finite-moment interpretation of the printed Lemma E.1.
The only additional numerical qualification is `0 ≤ A`; integrability
expresses genuine finite expectations rather than totalized integrals. -/
def ExpectedMaximumEnvelopeBound (q C : ℝ) : Prop :=
  ∀ (p n : ℕ), 1 ≤ p →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → Vector p), (∀ i, Measurable (Y i)) → iIndepFun Y μ →
    (∀ i j, (∫ ω, Y i ω j ∂μ)=0) →
  ∀ (A v : ℝ), 0 ≤ A →
    (∀ i, Integrable (fun ω => ‖Y i ω‖^q) μ) →
    ((∑ i, ∫ ω, ‖Y i ω‖^q ∂μ)≤A^q) →
    (∀ j, (∑ i, ∫ ω, Y i ω j^2 ∂μ)≤v) →
    (∫ ω, ‖sumVector Y ω‖ ∂μ) ≤ C *
      (Real.sqrt (v*dimensionLog p)+A*dimensionLog p^(1-1/q))

/-- Lemma E.1 with its necessary explicit nonnegative-envelope-scale
qualification. The positive coefficient precedes every model and budget. -/
theorem lemma_E1_expected_maximum (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ ExpectedMaximumEnvelopeBound.{u} q C := by
  refine ⟨envelopeMaximumConstant,zero_lt_one.trans_le one_le_envelopeMaximumConstant,?_⟩
  intro p n hp Ω mΩ μ hprob Y hY hind hcenter A v hA hmoment hbudget hvariance
  exact expected_maximum_under_envelope_moment μ Y hp hY hind hcenter hq hA hmoment hbudget hvariance

end
end RectangleCLTArxivV1

import RectangleCLTCompanion.SupportRows
import RectangleCLT.GaussianFaces
import RectangleCLT.BoundedCurvature
import RectangleCLT.ThinnedHypotheses

/-! Pointwise bounded representatives for the actual observations. All
changes occur on null sets, so the laws, moments and covariance budget are
preserved exactly. No inverse-eigenvalue loss enters the observable bound. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- A canonical support observation, modified only when its observable
projection violates the almost-sure envelope. -/
def boundedSupportObservation {Ω : Type*} {p q n : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (i : Fin n) (ω : Ω) : Vector q :=
  if ‖A.mulVec (whitenedObservation A ξ i ω)‖ ≤ δ then
    whitenedObservation A ξ i ω else 0

theorem boundedSupportObservation_projected_le {Ω : Type*} {p q n : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (ξ : Fin n → Ω → Vector p) {δ : ℝ} (hδ : 0 ≤ δ)
    (i : Fin n) (ω : Ω) : ‖A.mulVec (boundedSupportObservation A ξ δ i ω)‖ ≤ δ := by
  unfold boundedSupportObservation
  split_ifs with h
  · exact h
  · simpa only [Matrix.mulVec_zero, norm_zero] using hδ

variable {Ω : Type*} [MeasurableSpace Ω] {p q n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}

omit [IsProbabilityMeasure μ] in
theorem boundedSupportObservation_measurable
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin n) :
    Measurable (boundedSupportObservation A ξ δ i) := by
  have hm : Measurable (fun x : Vector q => A.mulVec x) := by
    apply measurable_pi_lambda
    intro j
    exact Finset.measurable_sum Finset.univ (fun k _ =>
      measurable_const.mul (measurable_pi_apply k))
  have hζ := whitenedObservation_measurable h A i
  exact Measurable.ite (measurableSet_le (hm.comp hζ).norm measurable_const) hζ measurable_const

theorem boundedSupportObservation_eq_ae
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) :
    boundedSupportObservation A ξ δ i =ᵐ[μ] whitenedObservation A ξ i := by
  filter_upwards [whitenedObservation_projected_bounded h A hA i] with ω hω
  exact if_pos hω

theorem boundedSupportObservation_reconstruct
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) :
    (fun ω => A.mulVec (boundedSupportObservation A ξ δ i ω)) =ᵐ[μ] ξ i := by
  filter_upwards [boundedSupportObservation_eq_ae h A hA i,
    whitenedObservation_reconstruct h A hA i] with ω hr hx
  rw [hr, hx]

/-- Every actual test integral is preserved, with no integrability loophole
or replacement law assumed. -/
theorem integral_boundedSupportObservation_comp
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) (f : Vector q → ℝ) :
    (∫ ω, f (boundedSupportObservation A ξ δ i ω) ∂μ) =
      ∫ ω, f (whitenedObservation A ξ i ω) ∂μ :=
  integral_congr_ae ((boundedSupportObservation_eq_ae h A hA i).fun_comp f)

theorem boundedSupportObservation_second_moments_integrable
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) (j k : Fin q) :
    Integrable (fun ω => boundedSupportObservation A ξ δ i ω j *
      boundedSupportObservation A ξ δ i ω k) μ := by
  apply ((whitenedObservation_hypotheses h A).integrable_coordinate_pair i j k).congr
  filter_upwards [boundedSupportObservation_eq_ae h A hA i] with ω hω
  rw [hω]

theorem boundedSupportObservation_covariance_budget
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (v : Vector q) :
    (∑ i, ∫ ω, (faceDot v (boundedSupportObservation A ξ δ i ω)) ^ 2 ∂μ) ≤
      vectorNormSq v := by
  calc
    _ = ∑ i, ∫ ω, (faceDot v (whitenedObservation A ξ i ω)) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_boundedSupportObservation_comp h A hA i (fun x => (faceDot v x) ^ 2)
    _ ≤ _ := whitenedObservation_covariance_budget h A hA v

/-- Retained observations are modified only outside their almost-sure
maximum-norm ball. This definition applies to every array point. -/
def boundedRetainedObservation {p n : ℕ} (δ : ℝ) (b : Fin n → Vector p) (i : Fin n) : Vector p :=
  if ‖b i‖ ≤ 2 * δ then b i else 0

theorem boundedRetainedObservation_norm_le {p n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (b : Fin n → Vector p) (i : Fin n) : ‖boundedRetainedObservation δ b i‖ ≤ 2 * δ := by
  unfold boundedRetainedObservation
  split_ifs with h
  · exact h
  · simpa only [norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ

theorem boundedRetainedObservation_measurable {p n : ℕ} (δ : ℝ) (i : Fin n) :
    Measurable (fun b : Fin n → Vector p => boundedRetainedObservation δ b i) :=
  Measurable.ite (measurableSet_le (measurable_pi_apply i).norm measurable_const)
    (measurable_pi_apply i) measurable_const

theorem boundedRetainedObservation_eq_ae
    (h : BoundedIndependentHypotheses μ ξ δ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun b : Fin n → Vector p => boundedRetainedObservation δ b) =ᵐ[bernoulliArrayLaw μ ξ t] id := by
  have hall := ae_all_iff.mpr (h.thinned t ht ht1).bounded
  filter_upwards [hall] with b hb
  funext i
  exact if_pos (hb i)

end
end RectangleCLT.Companion

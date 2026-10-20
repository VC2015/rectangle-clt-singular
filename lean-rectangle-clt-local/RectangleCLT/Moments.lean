import RectangleCLT.Statement
import Mathlib.Tactic.NormNum

/-!
# Elementary consequences of the bounded rectangle CLT hypotheses

This file establishes positivity of the envelope and integrability of coordinate
powers. Its elementary fourth-moment comparison uses coordinate second-moment
normalization. `Normalization.lean` now derives that normalization from
independence and unit coordinate variance, and proves the moment bounds.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

/-- A vector that vanishes almost everywhere has zero covariance. -/
theorem covariance_eq_zero_of_ae_eq_zero {Ω : Type u} [MeasurableSpace Ω]
    {p : ℕ} {μ : Measure Ω} {W : Ω → Vector p} (hW : W =ᵐ[μ] 0) :
    covariance μ W = 0 := by
  ext j k
  have hj : (∫ ω, W ω j ∂μ) = 0 := by
    calc
      (∫ ω, W ω j ∂μ) = ∫ _ω, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hW] with ω hω
        simp [hω]
      _ = 0 := integral_zero _ _
  have hjk : (∫ ω, W ω j * W ω k ∂μ) = 0 := by
    calc
      (∫ ω, W ω j * W ω k ∂μ) = ∫ _ω, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hW] with ω hω
        simp [hω]
      _ = 0 := integral_zero _ _
  simp only [covariance, hj, hjk, zero_mul, sub_zero, Matrix.zero_apply]

namespace BoundedHypotheses

variable {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ b : ℝ}

/-- In positive dimension, a unit covariance diagonal excludes a zero envelope.
This proof only uses boundedness and the unit diagonal, not independence. -/
theorem delta_pos (h : BoundedHypotheses μ ξ δ b) (hp : 1 ≤ p) : 0 < δ := by
  by_contra hnot
  have hδ : δ = 0 := le_antisymm (le_of_not_gt hnot) h.delta_nonneg
  have hξ : ∀ i, ξ i =ᵐ[μ] 0 := by
    intro i
    filter_upwards [h.bounded i] with ω hω
    exact norm_eq_zero.mp (le_antisymm (by simpa only [hδ] using hω) (norm_nonneg _))
  have hall : ∀ᵐ ω ∂μ, ∀ i, ξ i ω = 0 := ae_all_iff.mpr hξ
  have hsum : sumVector ξ =ᵐ[μ] 0 := by
    filter_upwards [hall] with ω hω
    simp [sumVector, hω]
  let j : Fin p := ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hp⟩
  have hunit := h.unit_diagonal j
  rw [covariance_eq_zero_of_ae_eq_zero hsum] at hunit
  norm_num at hunit

/-- Every coordinate inherits the same almost-everywhere envelope from the
finite-product maximum norm. -/
theorem abs_coordinate_le (h : BoundedHypotheses μ ξ δ b)
    (i : Fin n) (j : Fin p) : ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ := by
  filter_upwards [h.bounded i] with ω hω
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (ξ i ω) j).trans hω

/-- All natural coordinate powers are integrable on a finite measure space. -/
theorem integrable_coordinate_pow [IsFiniteMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) (i : Fin n) (j : Fin p) (m : ℕ) :
    Integrable (fun ω => (ξ i ω j) ^ m) μ := by
  apply (integrable_const (δ ^ m)).mono'
    (((measurable_pi_apply j).comp (h.measurable i)).pow_const m).aestronglyMeasurable
  filter_upwards [h.abs_coordinate_le i j] with ω hω
  simpa only [Real.norm_eq_abs, abs_pow] using
    pow_le_pow_left₀ (abs_nonneg (ξ i ω j)) hω m

/-- Every finite product of coordinates of one observation is integrable.
The tuple may repeat coordinates, so this covers all mixed moments. -/
theorem integrable_coordinate_product [IsFiniteMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) (i : Fin n) {m : ℕ}
    (J : Fin m → Fin p) :
    Integrable (fun ω => ∏ a : Fin m, ξ i ω (J a)) μ := by
  have hmeas : Measurable (fun ω => ∏ a : Fin m, ξ i ω (J a)) :=
    Finset.measurable_prod Finset.univ fun a _ =>
      (measurable_pi_apply (J a)).comp (h.measurable i)
  apply (integrable_const (δ ^ m)).mono' hmeas.aestronglyMeasurable
  filter_upwards [h.bounded i] with ω hω
  have hcoord : ∀ a : Fin m, |ξ i ω (J a)| ≤ δ := by
    intro a
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (ξ i ω) (J a)).trans hω
  have hprod : (∏ a : Fin m, |ξ i ω (J a)|) ≤ ∏ _a : Fin m, δ :=
    Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun a _ => hcoord a
  simpa only [Real.norm_eq_abs, Finset.abs_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hprod

/-- In particular, the mixed third moments in `gamma3` are integrable. -/
theorem integrable_coordinate_triple [IsFiniteMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) (i : Fin n) (j k l : Fin p) :
    Integrable (fun ω => ξ i ω j * ξ i ω k * ξ i ω l) μ := by
  simpa [Fin.prod_univ_succ, mul_assoc] using
    h.integrable_coordinate_product i (![j, k, l] : Fin 3 → Fin p)

/-- The pointwise envelope turns a coordinate fourth moment into its second
moment multiplied by `δ²`. -/
theorem fourthMoment_le_delta_sq_mul_secondMoment [IsFiniteMeasure μ]
    (h : BoundedHypotheses μ ξ δ b) (i : Fin n) (j : Fin p) :
    (∫ ω, (ξ i ω j) ^ 4 ∂μ) ≤ δ ^ 2 * ∫ ω, (ξ i ω j) ^ 2 ∂μ := by
  have hint := integral_mono_ae (h.integrable_coordinate_pow i j 4)
    ((h.integrable_coordinate_pow i j 2).const_mul (δ ^ 2))
  rw [← integral_const_mul]
  apply hint
  filter_upwards [h.abs_coordinate_le i j] with ω hω
  have hsq : (ξ i ω j) ^ 2 ≤ δ ^ 2 := by
    nlinarith [sq_abs (ξ i ω j), abs_nonneg (ξ i ω j), h.delta_nonneg]
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (ξ i ω j))
  nlinarith

/-- A fourth-moment bound conditional on explicit normalization of the summed
coordinate second moments. No unproved covariance identity is used here. -/
theorem gamma4_le_delta_sq_of_second_moments [IsFiniteMeasure μ]
    (h : BoundedHypotheses μ ξ δ b)
    (hsecond : ∀ j : Fin p, ∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ = 1) :
    gamma4 μ ξ ≤ δ ^ 2 := by
  unfold gamma4
  apply (Finset.fold_max_le (δ ^ 2)).mpr
  refine ⟨sq_nonneg δ, ?_⟩
  intro j _
  calc
    (∑ i, ∫ ω, (ξ i ω j) ^ 4 ∂μ) ≤
        ∑ i, δ ^ 2 * ∫ ω, (ξ i ω j) ^ 2 ∂μ := by
      exact Finset.sum_le_sum fun i _ => h.fourthMoment_le_delta_sq_mul_secondMoment i j
    _ = δ ^ 2 := by rw [← Finset.mul_sum, hsecond j, mul_one]

end BoundedHypotheses

end RectangleCLT

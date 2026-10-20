import RectangleCLT.BernoulliAggregate
import RectangleCLT.BernoulliCommonPoint
import RectangleCLT.BernoulliComparisonFinal
import RectangleCLT.IndependentCovariance
import RectangleCLT.BernoulliCubicBound

/-! Bounds for the actual common-point Bernoulli comparison. The envelopes
below bound the actual convolution derivatives on the stated local cubes. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT

theorem maskObservationSum_eq_leaveOne_add
    {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (mask : Kane.Cube n) (i : Fin n) (ω : Ω) :
    maskObservationSum ξ mask ω =
      maskObservationSum ξ (Function.update mask i false) ω + (if mask i then ξ i ω else 0) := by
  simpa only [Function.update_eq_self] using maskObservationSum_update_add ξ mask i (mask i) ω

theorem norm_retained_shift_le_two_delta
    {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (mask : Kane.Cube n) (i : Fin n) (ω : Ω) {δ t : ℝ}
    (hδ : 0 ≤ δ) (hξ : ‖ξ i ω‖ ≤ δ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖thinningScale t • (if mask i then ξ i ω else 0)‖ ≤ 2 * δ := by
  cases hi : mask i
  · simp only [hi, Bool.false_eq_true, ↓reduceIte, smul_zero, norm_zero]
    positivity
  · simp only [hi, ↓reduceIte, norm_smul, Real.norm_eq_abs,
      abs_of_pos (thinningScale_pos ht)]
    exact mul_le_mul (thinningScale_le_two ht1) hξ (norm_nonneg _) (by norm_num)

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- A local fourth-derivative envelope at the full selector point also bounds
the radius-`2δ` Taylor cube at each leave-one-out point. -/
theorem fourth_envelope_at_leaveOne
    {Ω : Type u} {n : ℕ} (ξ : Fin n → Ω → Vector p)
    (mask : Kane.Cube n) (i : Fin n) (ω : Ω) (x : Vector p) {δ t : ℝ}
    (hδ : 0 ≤ δ) (hξ : ‖ξ i ω‖ ≤ δ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ y z : Vector p, ‖z‖ ≤ 4 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν (y + z) j k l m| ≤ H y j k l m) :
    ∀ z : Vector p, ‖z‖ ≤ 2 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω + z)
          j k l m| ≤ H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m := by
  let u := thinningScale t • (if mask i then ξ i ω else 0)
  have hu : ‖u‖ ≤ 2 * δ := norm_retained_shift_le_two_delta ξ mask i ω hδ hξ ht ht1
  have hpoint : x + thinningScale t • maskObservationSum ξ mask ω =
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) + u := by
    rw [maskObservationSum_eq_leaveOne_add ξ mask i ω, smul_add]
    dsimp [u]
    abel
  intro z hz j k l m
  have heq : x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω + z =
      (x + thinningScale t • maskObservationSum ξ mask ω) + (z - u) := by
    rw [hpoint]
    abel
  rw [heq]
  apply hH _ _ _ j k l m
  exact (norm_sub_le z u).trans ((add_le_add hz hu).trans (by linarith))

/-- Actual corrected residuals, with their different leave-one-out points,
sum against the same envelope at the full random selector point. -/
theorem ae_sum_abs_correctedResidual_leaveOne_le_gamma4
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (mask : Kane.Cube n) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ y z : Vector p, ‖z‖ ≤ 4 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν (y + z) j k l m| ≤ H y j k l m) :
    ∀ᵐ ω ∂μ,
      (∑ i, |s.correctedOneObservationResidual ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t|) ≤
      6 * gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m,
        H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, ‖ξ i ω‖ ≤ δ := ae_all_iff.mpr hbound
  filter_upwards [hall] with ω hω
  let y := x + thinningScale t • maskObservationSum ξ mask ω
  have hH0 (j k l m : Fin p) : 0 ≤ H y j k l m := by
    have hh := hH y 0 (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hδ) j k l m
    exact (abs_nonneg _).trans (by simpa only [add_zero] using hh)
  calc
    _ ≤ ∑ i, 6 * fourthCoordinateMoment μ (ξ i) (H y) := by
      apply Finset.sum_le_sum
      intro i _
      exact s.abs_correctedOneObservationResidual_le ν μ (ξ i) (hξ i) hδ
        (hbound i) (hcenter i) _ ht ht1 (H y)
        (s.fourth_envelope_at_leaveOne ν ξ mask i ω x hδ (hω i) ht ht1 H hH)
    _ = 6 * ∑ i, fourthCoordinateMoment μ (ξ i) (H y) := by rw [Finset.mul_sum]
    _ ≤ 6 * (gamma4 μ ξ * (∑ j, ∑ k, ∑ l, ∑ m, H y j k l m)) :=
      mul_le_mul_of_nonneg_left (sum_fourthCoordinateMoment_le_gamma4 μ ξ (H y) hH0) (by norm_num)
    _ = _ := by ring

noncomputable def selectorFourthEnvelopeAverage
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (t : ℝ)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ) : ℝ :=
  ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ ω, ∑ j, ∑ k, ∑ l, ∑ m,
      H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m ∂μ

/-- The actual integrated residual is controlled by the full-point local
fourth-derivative envelope, with constant six and aggregate `gamma4`. -/
theorem abs_selectorCorrectedResidual_le_gamma4
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ y z : Vector p, ‖z‖ ≤ 4 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative ν (y + z) j k l m| ≤ H y j k l m)
    (hHi : ∀ mask : Kane.Cube n, Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m,
      H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m) μ) :
    |s.selectorCorrectedResidual ν μ ξ x t| ≤
      6 * gamma4 μ ξ * selectorFourthEnvelopeAverage μ ξ x t H := by
  let R := fun (mask : Kane.Cube n) (i : Fin n) (ω : Ω) =>
    s.correctedOneObservationResidual ν μ (ξ i)
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t
  have hRi (mask : Kane.Cube n) (i : Fin n) : Integrable (R mask i) μ :=
    s.integrable_correctedOneObservationResidual_base ν μ (ξ i) _ (hξ i)
      (measurable_const.add (measurable_const.smul
        (measurable_maskObservationSum ξ hξ (Function.update mask i false))))
      hδ (hbound i) ht
  have hm (mask : Kane.Cube n) :
      |∑ i, ∫ ω, R mask i ω ∂μ| ≤ 6 * gamma4 μ ξ *
        ∫ ω, ∑ j, ∑ k, ∑ l, ∑ m,
          H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m ∂μ := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hRi mask i)]
    have hb := s.ae_sum_abs_correctedResidual_leaveOne_le_gamma4 ν μ ξ hξ hδ
      hbound hcenter mask x ht ht1 H hH
    have hn := norm_integral_le_of_norm_le ((hHi mask).const_mul (6 * gamma4 μ ξ))
      (hb.mono (fun ω hω => by
        change ‖∑ i, R mask i ω‖ ≤ _
        have hs : |∑ i, R mask i ω| ≤ ∑ i, |R mask i ω| := Finset.abs_sum_le_sum_abs _ _
        have hs' : ‖∑ i, R mask i ω‖ ≤ ∑ i, |R mask i ω| := by
          simpa only [Real.norm_eq_abs] using hs
        exact hs'.trans hω))
    simpa only [Real.norm_eq_abs, integral_const_mul] using hn
  unfold selectorCorrectedResidual
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    _ ≤ ∑ mask : Kane.Cube n,
        |Kane.maskWeight (thinningProbability t) mask * ∑ i, ∫ ω, R mask i ω ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask *
        (6 * gamma4 μ ξ * ∫ ω, ∑ j, ∑ k, ∑ l, ∑ m,
          H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m ∂μ) := by
      apply Finset.sum_le_sum
      intro mask _
      rw [abs_mul, abs_of_nonneg (Kane.maskWeight_nonneg
        (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)]
      exact mul_le_mul_of_nonneg_left (hm mask) (Kane.maskWeight_nonneg
        (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)
    _ = _ := by
      unfold selectorFourthEnvelopeAverage
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mask _
      ring

omit [IsProbabilityMeasure ν] in
/-- The matched-covariance Bernoulli comparison for the actual path. The
fourth-order input is an envelope of actual convolution derivatives on the
full radius-`4δ` cube, rather than a premise about the path derivative. -/
theorem abs_selectorHeatDerivative_le_comparison
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ y z : Vector p, ‖z‖ ≤ 4 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (y + z) j k l m| ≤
        H y j k l m)
    (hHi : ∀ mask : Kane.Cube n, Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m,
      H (x + thinningScale t • maskObservationSum ξ mask ω) j k l m) μ) :
    |s.selectorHeatDerivative μ ξ A x t| ≤
      t / 3 * gamma3 μ ξ *
        s.selectorThirdAbsoluteAverage (gaussianLaw (Real.sqrt t • A)) μ ξ x
          (thinningProbability t) (thinningScale t) +
      6 * gamma4 μ ξ * selectorFourthEnvelopeAverage μ ξ x t H := by
  exact (s.abs_selectorHeatDerivative_le_cubic_add_residual μ ξ h A hA x ht ht1).trans
    (add_le_add_left (s.abs_selectorCorrectedResidual_le_gamma4
      (gaussianLaw (Real.sqrt t • A)) μ ξ h.measurable h.delta_nonneg h.bounded h.centered
      x ht ht1 H hH hHi) _)

end FaceSmoother
end RectangleCLT

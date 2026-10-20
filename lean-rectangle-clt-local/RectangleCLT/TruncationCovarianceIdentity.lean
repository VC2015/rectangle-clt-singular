import RectangleCLT.TruncationBasic
import RectangleCLT.TruncationTailMoments

/-!
# Actual covariance identities for centered truncation

All covariance matrices here are computed from the original random
vectors and their actual integrals.
-/

open MeasureTheory

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Translating a random vector by a constant leaves its actual covariance
unchanged. -/
theorem covariance_sub_const [IsProbabilityMeasure μ]
    {p : ℕ} {Y : Ω → Vector p}
    (hY : ∀ j, Integrable (fun ω => Y ω j) μ)
    (hYY : ∀ j k, Integrable (fun ω => Y ω j * Y ω k) μ) (c : Vector p) :
    covariance μ (fun ω => Y ω - c) = covariance μ Y := by
  have hm (j : Fin p) : (∫ ω, (Y ω - c) j ∂μ) =
      (∫ ω, Y ω j ∂μ) - c j := by
    change (∫ ω, Y ω j - c j ∂μ) = _
    rw [integral_sub (hY j) (integrable_const _)]
    simp
  have hp (j k : Fin p) : (∫ ω, (Y ω - c) j * (Y ω - c) k ∂μ) =
      (∫ ω, Y ω j * Y ω k ∂μ) - c j * (∫ ω, Y ω k ∂μ) -
        c k * (∫ ω, Y ω j ∂μ) + c j * c k := by
    calc
      _ = ∫ ω, Y ω j * Y ω k - c j * Y ω k - c k * Y ω j + c j * c k ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring
      _ = _ := by
        rw [integral_add (((hYY j k).sub ((hY k).const_mul _)).sub
          ((hY j).const_mul _)) (integrable_const _),
          integral_sub ((hYY j k).sub ((hY k).const_mul _)) ((hY j).const_mul _),
          integral_sub (hYY j k) ((hY k).const_mul _)]
        simp
  ext j k
  simp only [covariance, hp, hm]
  ring

/-- The covariance loss under one whole-vector truncation is the discarded
second-moment matrix plus the outer product of the removed mean. -/
theorem truncation_covariance_deficit [IsProbabilityMeasure μ]
    {p : ℕ} {Y : Ω → Vector p} (hY : Measurable Y)
    (hYY : ∀ j k, Integrable (fun ω => Y ω j * Y ω k) μ)
    (hcenter : ∀ j, (∫ ω, Y ω j ∂μ) = 0) (u : ℝ) (j k : Fin p) :
    covariance μ Y j k - covariance μ (fun ω => truncateVector u (Y ω)) j k =
      (∫ ω, {x | ‖Y x‖ ≤ u}ᶜ.indicator
        (fun x => Y x j * Y x k) ω ∂μ) +
        truncationMean μ Y u j * truncationMean μ Y u k := by
  have hA : MeasurableSet {ω | ‖Y ω‖ ≤ u} :=
    measurableSet_le hY.norm measurable_const
  have hp : (fun ω => truncateVector u (Y ω) j * truncateVector u (Y ω) k) =
      {ω | ‖Y ω‖ ≤ u}.indicator (fun ω => Y ω j * Y ω k) := by
    funext ω
    by_cases hω : ‖Y ω‖ ≤ u <;> simp [truncateVector, hω]
  have hsplit := integral_add_compl hA (hYY j k)
  rw [← integral_indicator hA, ← integral_indicator hA.compl] at hsplit
  simp only [covariance, hcenter, zero_mul, sub_zero, hp, truncationMean]
  linarith

/-- Centering the truncated vector leaves precisely the same covariance. -/
theorem covariance_centeredTruncateVector [IsProbabilityMeasure μ]
    {p : ℕ} {Y : Ω → Vector p} (hY : Measurable Y) {u : ℝ} (hu : 0 ≤ u) :
    covariance μ (centeredTruncateVector μ Y u) =
      covariance μ (fun ω => truncateVector u (Y ω)) := by
  apply covariance_sub_const (fun j => integrable_truncateVector_coordinate hY hu j)
  intro j k
  apply (integrable_const (u * u)).mono'
    ((((measurable_pi_apply j).comp ((measurable_truncateVector u).comp hY)).mul
      ((measurable_pi_apply k).comp ((measurable_truncateVector u).comp hY))).aestronglyMeasurable)
  exact ae_of_all _ fun ω => by
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul
      (by simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (truncateVector u (Y ω)) j).trans (norm_truncateVector_le hu _))
      (by simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (truncateVector u (Y ω)) k).trans (norm_truncateVector_le hu _))
      (abs_nonneg _) hu

end

end RectangleCLT

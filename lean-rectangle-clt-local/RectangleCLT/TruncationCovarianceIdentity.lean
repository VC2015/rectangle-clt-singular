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
        rw [integral_add
          (f := fun ω => Y ω j * Y ω k - c j * Y ω k - c k * Y ω j)
          (g := fun _ => c j * c k)
          (((hYY j k).sub ((hY k).const_mul (c j))).sub
            ((hY j).const_mul (c k))) (integrable_const _),
          integral_sub (f := fun ω => Y ω j * Y ω k - c j * Y ω k)
            (g := fun ω => c k * Y ω j)
            ((hYY j k).sub ((hY k).const_mul (c j))) ((hY j).const_mul (c k)),
          integral_sub (f := fun ω => Y ω j * Y ω k) (g := fun ω => c j * Y ω k)
            (hYY j k) ((hY k).const_mul (c j))]
        simp [integral_const_mul]
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

/-- Cauchy--Schwarz for entries of the actual covariance matrix, including
singular covariance matrices. -/
theorem covariance_entry_le_standard_deviations [IsProbabilityMeasure μ]
    {p : ℕ} {Y : Ω → Vector p}
    (hLp : ∀ j, MemLp (fun ω => Y ω j) 2 μ) (j k : Fin p) :
    |covariance μ Y j k| ≤
      Real.sqrt (covariance μ Y j j) * Real.sqrt (covariance μ Y k k) := by
  let m : Vector p := fun j => ∫ ω, Y ω j ∂μ
  let Z : Ω → Vector p := fun ω => Y ω - m
  have hZLp (j : Fin p) : MemLp (fun ω => Z ω j) 2 μ :=
    (hLp j).sub (memLp_const _)
  have hZmean (j : Fin p) : (∫ ω, Z ω j ∂μ) = 0 := by
    change (∫ ω, Y ω j - m j ∂μ) = 0
    rw [integral_sub ((hLp j).integrable (by norm_num)) (integrable_const _)]
    simp [m]
  have hmat : covariance μ Z = covariance μ Y :=
    covariance_sub_const (fun j => (hLp j).integrable (by norm_num))
      (fun j k => (hLp j).integrable_mul (hLp k)) m
  have heq (j k : Fin p) : covariance μ Y j k = ∫ ω, Z ω j * Z ω k ∂μ := by
    rw [← hmat]
    simp only [covariance, hZmean, zero_mul, sub_zero]
  have hZ2 (j : Fin p) : Integrable (fun ω => Z ω j ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hZLp j).aestronglyMeasurable).mp (hZLp j)
  have hnonneg (j : Fin p) : 0 ≤ covariance μ Y j j := by
    rw [heq]
    exact integral_nonneg fun ω => mul_self_nonneg _
  have hc := integral_product_sq_le (hZ2 j) (hZ2 k)
    ((hZLp j).integrable_mul (hZLp k))
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (hnonneg j), Real.sq_sqrt (hnonneg k), heq j k,
    heq j j, heq k k]
  simpa only [pow_two] using hc

end

end RectangleCLT

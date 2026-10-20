import RectangleCLTCompanion.SubexponentialStatement
import RectangleCLTCompanion.SubexponentialClipping
import RectangleCLT.BoundedIndependentScaling
import Mathlib.Probability.Variance

/-! Actual clipped and residual arrays.  The clipping is performed on each
observation before summing, so independence of the rows is preserved. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}

def centeredClippedRows (μ : Measure Ω) (X : Fin n → Ω → Vector p) (T : ℝ) :
    Fin n → Ω → Vector p :=
  fun i ω j => clipAt T (X i ω j) - ∫ a, clipAt T (X i a j) ∂μ

def centeredResidualRows (μ : Measure Ω) (X : Fin n → Ω → Vector p) (T : ℝ) :
    Fin n → Ω → Vector p :=
  fun i ω j => clipResidual T (X i ω j) - ∫ a, clipResidual T (X i a j) ∂μ

def normalizedClippedRows (μ : Measure Ω) (X : Fin n → Ω → Vector p) (T : ℝ) :
    Fin n → Ω → Vector p :=
  fun i ω => (Real.sqrt (n : ℝ))⁻¹ • centeredClippedRows μ X T i ω

def normalizedResidualRows (μ : Measure Ω) (X : Fin n → Ω → Vector p) (T : ℝ) :
    Fin n → Ω → Vector p :=
  fun i ω => (Real.sqrt (n : ℝ))⁻¹ • centeredResidualRows μ X T i ω

theorem SubexponentialIndependentHypotheses.coordinate_exponentialMomentBound
    {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (i : Fin n) (j : Fin p) :
    ExponentialMomentBound μ (fun ω => X i ω j) K := by
  exact ⟨(measurable_pi_apply j).comp (h.measurable i),
    lt_of_lt_of_le zero_lt_one h.one_le_scale,
    h.integrable_exp i j, h.exponential_moment i j⟩

theorem integrable_clipped_coordinate [IsFiniteMeasure μ]
    {X : Fin n → Ω → Vector p} (hX : ∀ i, Measurable (X i))
    {T : ℝ} (hT : 0 ≤ T) (i : Fin n) (j : Fin p) :
    Integrable (fun ω => clipAt T (X i ω j)) μ := by
  apply (integrable_const T).mono'
    ((clipAt_continuous T).measurable.comp ((measurable_pi_apply j).comp (hX i))).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using abs_clipAt_le hT (X i ω j))

theorem abs_integral_clipped_coordinate [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {T : ℝ} (hT : 0 ≤ T)
    (i : Fin n) (j : Fin p) :
    |∫ ω, clipAt T (X i ω j) ∂μ| ≤ T := by
  have hh := norm_integral_le_of_norm_le_const
    (μ := μ) (ae_of_all _ (fun ω => by
      simpa only [Real.norm_eq_abs] using abs_clipAt_le hT (X i ω j)))
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using hh

theorem centeredClippedRows_measurable
    {X : Fin n → Ω → Vector p} (hX : ∀ i, Measurable (X i))
    (T : ℝ) (i : Fin n) : Measurable (centeredClippedRows μ X T i) := by
  apply measurable_pi_iff.mpr
  intro j
  exact ((clipAt_continuous T).measurable.comp
    ((measurable_pi_apply j).comp (hX i))).sub_const _

theorem centeredResidualRows_measurable
    {X : Fin n → Ω → Vector p} (hX : ∀ i, Measurable (X i))
    (T : ℝ) (i : Fin n) : Measurable (centeredResidualRows μ X T i) := by
  apply measurable_pi_iff.mpr
  intro j
  exact ((clipResidual_continuous T).measurable.comp
    ((measurable_pi_apply j).comp (hX i))).sub_const _

theorem centeredClippedRows_independent
    {X : Fin n → Ω → Vector p} (hind : iIndepFun X μ) (T : ℝ) :
    iIndepFun (centeredClippedRows μ X T) μ := by
  exact hind.comp (fun i (x : Vector p) => fun j =>
      clipAt T (x j) - ∫ a, clipAt T (X i a j) ∂μ)
    (fun i => measurable_pi_iff.mpr (fun j =>
      ((clipAt_continuous T).measurable.comp (measurable_pi_apply j)).sub_const _))

theorem centeredResidualRows_independent
    {X : Fin n → Ω → Vector p} (hind : iIndepFun X μ) (T : ℝ) :
    iIndepFun (centeredResidualRows μ X T) μ := by
  exact hind.comp (fun i (x : Vector p) => fun j =>
      clipResidual T (x j) - ∫ a, clipResidual T (X i a j) ∂μ)
    (fun i => measurable_pi_iff.mpr (fun j =>
      ((clipResidual_continuous T).measurable.comp (measurable_pi_apply j)).sub_const _))

theorem centeredClippedRows_centered [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} (hX : ∀ i, Measurable (X i))
    {T : ℝ} (hT : 0 ≤ T) (i : Fin n) (j : Fin p) :
    (∫ ω, centeredClippedRows μ X T i ω j ∂μ) = 0 := by
  simp only [centeredClippedRows]
  rw [integral_sub (integrable_clipped_coordinate hX hT i j) (integrable_const _)]
  simp

theorem centeredClippedRows_norm_le [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {T : ℝ} (hT : 0 ≤ T) (i : Fin n) (ω : Ω) :
    ‖centeredClippedRows μ X T i ω‖ ≤ 2 * T := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hT)).mpr
  intro j
  change |clipAt T (X i ω j) - ∫ a, clipAt T (X i a j) ∂μ| ≤ 2 * T
  exact (abs_sub _ _).trans (by
    have h₁ := abs_clipAt_le hT (X i ω j)
    have h₂ := abs_integral_clipped_coordinate (μ := μ) (X := X) hT i j
    linarith)

theorem centeredClippedRows_boundedHypotheses [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {T : ℝ} (hT : 0 ≤ T) :
    BoundedIndependentHypotheses μ (centeredClippedRows μ X T) (2 * T) := by
  exact ⟨centeredClippedRows_measurable hX T,
    centeredClippedRows_independent hind T,
    centeredClippedRows_centered hX hT,
    fun i => ae_of_all _ (centeredClippedRows_norm_le hT i),
    mul_nonneg (by norm_num) hT⟩

theorem normalizedClippedRows_boundedHypotheses [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {T : ℝ} (hT : 0 ≤ T) :
    BoundedIndependentHypotheses μ (normalizedClippedRows μ X T)
      (2 * T / Real.sqrt (n : ℝ)) := by
  have hh := (centeredClippedRows_boundedHypotheses hX hind hT).smul_of_nonneg
    (Real.sqrt (n : ℝ))⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  simpa only [normalizedClippedRows, div_eq_mul_inv, mul_comm] using hh

theorem centeredResidualRows_centered [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (i : Fin n) (j : Fin p) :
    (∫ ω, centeredResidualRows μ X (K * u) i ω j ∂μ) = 0 := by
  simp only [centeredResidualRows]
  rw [integral_sub ((h.coordinate_exponentialMomentBound i j).integrable_residual hu)
    (integrable_const _)]
  simp

theorem centeredClippedRows_add_centeredResidualRows [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (i : Fin n) (ω : Ω) :
    centeredClippedRows μ X (K * u) i ω + centeredResidualRows μ X (K * u) i ω = X i ω := by
  ext j
  have hi := (h.coordinate_exponentialMomentBound i j).integrable
  have hc := integrable_clipped_coordinate h.measurable
    (mul_nonneg (zero_le_one.trans h.one_le_scale) hu) i j
  have hm : (∫ a, clipResidual (K * u) (X i a j) ∂μ) =
      -(∫ a, clipAt (K * u) (X i a j) ∂μ) := by
    simp only [clipResidual]
    rw [integral_sub hi hc, h.centered i j, zero_sub]
  simp only [Pi.add_apply, centeredClippedRows, centeredResidualRows, hm, clipResidual]
  ring

theorem normalizedObservationSum_eq_clipped_add_residual [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u) (ω : Ω) :
    normalizedObservationSum X ω =
      sumVector (normalizedClippedRows μ X (K * u)) ω +
      sumVector (normalizedResidualRows μ X (K * u)) ω := by
  simp only [normalizedObservationSum, normalizedClippedRows, normalizedResidualRows,
    sumVector_smul, ← smul_add]
  congr 1
  simp only [sumVector, ← Finset.sum_add_distrib,
    centeredClippedRows_add_centeredResidualRows h hu]

end
end RectangleCLT.Companion

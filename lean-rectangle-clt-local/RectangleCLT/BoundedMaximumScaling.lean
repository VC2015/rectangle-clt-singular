import RectangleCLT.BoundedMaximum
import RectangleCLT.IndependentCovariance

/-! The expected-maximum bound with arbitrary positive common coordinate
variance, obtained from the actual normalized sum. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.BoundedIndependentHypotheses

theorem integral_norm_sum_le_of_variance
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) :
    (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
      2 * Real.sqrt v * Real.sqrt (dimensionLog p) + 2 * δ * dimensionLog p := by
  let a := (Real.sqrt v)⁻¹
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have ha : 0 < a := inv_pos.mpr hsv
  let ζ : Fin n → Ω → Vector p := fun i ω => a • ξ i ω
  have hz : BoundedIndependentHypotheses μ ζ (a * δ) := by
    refine ⟨?_, ?_, ?_, ?_, mul_nonneg ha.le h.delta_nonneg⟩
    · intro i
      exact measurable_const.smul (h.measurable i)
    · exact h.independent.comp (fun _ x => a • x)
        (fun _ => measurable_const.smul measurable_id)
    · intro i j
      change (∫ ω, a * ξ i ω j ∂μ) = 0
      rw [integral_const_mul, h.centered i j, mul_zero]
    · intro i
      filter_upwards [h.bounded i] with ω hω
      change ‖a • ξ i ω‖ ≤ a * δ
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left hω ha.le
  have hcov : ∀ j, covariance μ (sumVector ζ) j j = 1 := by
    intro j
    rw [hz.covariance_sum]
    have heq (i : Fin n) : (∫ ω, ζ i ω j * ζ i ω j ∂μ) =
        a ^ 2 * (∫ ω, ξ i ω j * ξ i ω j ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      change (a * ξ i ω j) * (a * ξ i ω j) = _
      ring
    simp_rw [heq]
    rw [← Finset.mul_sum, ← h.covariance_sum, hdiag j]
    dsimp [a]
    rw [inv_pow, inv_mul_eq_div, Real.sq_sqrt hv.le, div_self hv.ne']
  have hsum (ω : Ω) : sumVector ζ ω = a • sumVector ξ ω := by
    simp only [sumVector, ζ, Finset.smul_sum]
  have hint : (∫ ω, ‖sumVector ζ ω‖ ∂μ) =
      a * (∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
    simp_rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact integral_const_mul _ _
  have hh := hz.integral_norm_sum_le hp hcov
  rw [hint] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hsv.le
  have hcancel : Real.sqrt v * a = 1 := mul_inv_cancel₀ hsv.ne'
  have heq : Real.sqrt v * (2 * Real.sqrt (dimensionLog p) +
      2 * (a * δ) * dimensionLog p) =
      2 * Real.sqrt v * Real.sqrt (dimensionLog p) + 2 * δ * dimensionLog p := by
    calc
      _ = 2 * Real.sqrt v * Real.sqrt (dimensionLog p) +
          2 * (Real.sqrt v * a) * δ * dimensionLog p := by ring
      _ = _ := by rw [hcancel]; ring
  rw [← mul_assoc, hcancel, one_mul, heq] at hh'
  exact hh'

theorem norm_sum_tail_le_of_variance
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ v M : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) (hM : 0 < M) :
    μ.real {ω | M < ‖sumVector ξ ω‖} ≤
      (2 * Real.sqrt v * Real.sqrt (dimensionLog p) + 2 * δ * dimensionLog p) / M := by
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => norm_nonneg (sumVector ξ ω))
    h.integrable_norm_sum M
  have hset : {ω | M < ‖sumVector ξ ω‖} ⊆ {ω | M ≤ ‖sumVector ξ ω‖} := by
    intro ω hx
    change M ≤ ‖sumVector ξ ω‖
    exact (show M < ‖sumVector ξ ω‖ from hx).le
  have htail := measureReal_mono (μ := μ) hset
  apply (le_div_iff₀ hM).mpr
  have hh := mul_le_mul_of_nonneg_right htail hM.le
  have hh' : μ.real {ω | M ≤ ‖sumVector ξ ω‖} * M ≤
      (∫ ω, ‖sumVector ξ ω‖ ∂μ) := by simpa only [mul_comm] using hMarkov
  exact hh.trans (hh'.trans (h.integral_norm_sum_le_of_variance hp hv hdiag))

end RectangleCLT.BoundedIndependentHypotheses

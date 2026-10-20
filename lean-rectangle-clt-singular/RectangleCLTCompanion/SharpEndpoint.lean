import RectangleCLTCompanion.CoarseBound
import RectangleCLT.BoundedCurvature
import RectangleCLT.GaussianCurvature

/-! Endpoint smoothing with the minimum of the covariance-free logarithmic
bound and the positive pair-gap bound. The rectangle transfer preserves every
endpoint convention and allows atoms on the bounded endpoint. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable def sharpEndpointConstant : ℝ := endpointConstant + (8 * Real.exp 4 + 4)

theorem sharpEndpointConstant_nonneg : 0 ≤ sharpEndpointConstant := by
  unfold sharpEndpointConstant
  have hh := endpointConstant_nonneg
  positivity

theorem endpointConstant_le_sharpEndpointConstant : endpointConstant ≤ sharpEndpointConstant := by
  unfold sharpEndpointConstant
  have he := Real.exp_pos (4 : ℝ)
  linarith

theorem gapEndpointConstant_le_sharpEndpointConstant :
    8 * Real.exp 4 + 4 ≤ sharpEndpointConstant := by
  unfold sharpEndpointConstant
  linarith [endpointConstant_nonneg]

end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem integral_endpoint_error_le_twice_kappa
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) :
    (∫ ω, |s.F (W ω) - s.indicator (W ω)| ∂μ) ≤ 2 * ∫ ω, s.kappa (W ω) ∂μ := by
  classical
  have hs : MeasurableSet {ω | s.Inside (W ω)} := s.measurableSet_Inside.preimage hW
  have hiI : Integrable (fun ω => s.indicator (W ω)) μ := by
    simpa only [indicator, Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ) (μ := μ)).indicator hs
  have hiF : Integrable (fun ω => s.F (W ω)) μ :=
    (integrable_const (1 : ℝ)).mono'
      (s.continuous_F.measurable.comp hW).aestronglyMeasurable
      (ae_of_all _ (fun ω => s.norm_F_le_one _))
  calc
    _ ≤ ∫ ω, 2 * s.kappa (W ω) ∂μ :=
      integral_mono (hiF.sub hiI).abs ((s.integrable_kappa hW).const_mul 2)
        (fun ω => s.endpoint_error (W ω))
    _ = _ := integral_const_mul _ _

/-- A positive pair gap controls both actual endpoint L1 errors, without a
positive smallest eigenvalue of the full covariance. -/
theorem bounded_gaussian_endpoint_error_le_pairGap
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hc : 0 < pairGap (covariance μ (sumVector ξ))) (hband : δ ≤ s.bandwidth)
    (r : Vector p) :
    (∫ ω, |s.F (sumVector ξ ω + r) - s.indicator (sumVector ξ ω + r)| ∂μ) +
      (∫ x : Vector p, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
      (8 * Real.exp 4 + 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
        pairGap (covariance μ (sumVector ξ)) := by
  have hb := (s.integral_endpoint_error_le_twice_kappa μ
    (fun ω => sumVector ξ ω + r) (h.measurable_sum.add_const r)).trans
      (mul_le_mul_of_nonneg_left (h.integral_kappa_le s r hp hunit hc hband) (by norm_num))
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact hunit j
  have hg := (s.integral_endpoint_error_le_twice_kappa (gaussianLaw A)
    (fun x => x + r) (measurable_id.add_const r)).trans
      (mul_le_mul_of_nonneg_left (s.gaussian_expected_kappa_le hp A r hdiag (by simpa only [hA] using hc))
        (by norm_num))
  rw [hA] at hg
  exact (add_le_add hb hg).trans_eq (by ring)

/-- The exact `κ=min(L,1/c)` improvement with the zero-gap fallback `L`.
No positive-gap assumption is imposed on the data. -/
theorem bounded_gaussian_endpoint_error_le_kappa
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (hband : δ ≤ s.bandwidth) (r : Vector p) :
    (∫ ω, |s.F (sumVector ξ ω + r) - s.indicator (sumVector ξ ω + r)| ∂μ) +
      (∫ x : Vector p, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
      Companion.sharpEndpointConstant * s.bandwidth * Real.sqrt (dimensionLog p) *
        Companion.kappa (dimensionLog p) (pairGap (covariance μ (sumVector ξ))) := by
  let c := pairGap (covariance μ (sumVector ξ))
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact hunit j
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hcoarse := s.bounded_gaussian_endpoint_error_le h hp hunit A hdiag hband r
  have hcoarse' :
      (∫ ω, |s.F (sumVector ξ ω + r) - s.indicator (sumVector ξ ω + r)| ∂μ) +
        (∫ x : Vector p, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
      Companion.sharpEndpointConstant * s.bandwidth * Real.sqrt (dimensionLog p) * dimensionLog p :=
    hcoarse.trans (by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right Companion.endpointConstant_le_sharpEndpointConstant
            s.bandwidth_pos.le) (Real.sqrt_nonneg _)) hL)
  by_cases hc : 0 < c
  · have hgap := s.bounded_gaussian_endpoint_error_le_pairGap h hp hunit A hA hc hband r
    have hgap' :
        (∫ ω, |s.F (sumVector ξ ω + r) - s.indicator (sumVector ξ ω + r)| ∂μ) +
          (∫ x : Vector p, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
        Companion.sharpEndpointConstant * s.bandwidth * Real.sqrt (dimensionLog p) * c⁻¹ := by
      apply hgap.trans
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right Companion.gapEndpointConstant_le_sharpEndpointConstant
            s.bandwidth_pos.le) (Real.sqrt_nonneg _)) (inv_nonneg.mpr hc.le)
    change _ ≤ Companion.sharpEndpointConstant * s.bandwidth * Real.sqrt (dimensionLog p) *
      (if 0 < c then min (dimensionLog p) c⁻¹ else dimensionLog p)
    rw [if_pos hc, mul_min_of_nonneg _ _ (by
      exact mul_nonneg (mul_nonneg Companion.sharpEndpointConstant_nonneg s.bandwidth_pos.le)
        (Real.sqrt_nonneg _))]
    exact le_min hcoarse' hgap'
  · change _ ≤ Companion.sharpEndpointConstant * s.bandwidth * Real.sqrt (dimensionLog p) *
      (if 0 < c then min (dimensionLog p) c⁻¹ else dimensionLog p)
    rw [if_neg hc]
    exact hcoarse'

end
end RectangleCLT.FaceSmoother

namespace RectangleCLT.Companion

noncomputable section

/-- Atom-safe transfer from a uniform actual closed-box smoother comparison
to all rectangles, with the sharp endpoint minimum and no gap hypothesis. -/
theorem rectangleError_le_smoother_gap_add_sharp_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (h : ℝ) (hh : 0 < h) (hband : δ ≤ h) (E : ℝ)
    (hgap : ∀ lo hi : Vector p, let s := FaceSmoother.closedBox lo hi h hh
      |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤ E)
    (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤ E + sharpEndpointConstant * h *
      Real.sqrt (dimensionLog p) * kappa (dimensionLog p) (pairGap (covariance μ (sumVector ξ))) := by
  apply rectangleError_le_of_closedBox hp μ (sumVector ξ) hdata.measurable_sum A _ R
  intro lo hi
  let s := FaceSmoother.closedBox lo hi h hh
  have he := s.bounded_gaussian_endpoint_error_le_kappa hdata hp hunit A hA hband 0
  simp only [add_zero] at he
  have hp' := s.probability_gap_le_smoother_gap_add_endpoint_errors μ (gaussianLaw A)
    (sumVector ξ) hdata.measurable_sum id measurable_id
  simp only [id_eq] at hp'
  rw [add_assoc] at hp'
  have hclosed := hp'.trans (add_le_add (hgap lo hi) he)
  have hμ : {ω | s.Inside (sumVector ξ ω)} = sumVector ξ ⁻¹' (Rect.closedBox lo hi).carrier := by
    ext ω
    exact FaceSmoother.closedBox_Inside lo hi h hh (sumVector ξ ω)
  have hG : {z | s.Inside z} = (Rect.closedBox lo hi).carrier := by
    ext z
    exact FaceSmoother.closedBox_Inside lo hi h hh z
  rw [hμ, hG] at hclosed
  exact hclosed

end
end RectangleCLT.Companion

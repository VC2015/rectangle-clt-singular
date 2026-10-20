import RectangleCLT.BoundedCurvature
import RectangleCLT.GaussianCurvature
import RectangleCLT.RectangleExtension
import RectangleCLT.RandomResampling

/-! Converting the actual smoothed comparison into rectangle probabilities.
Both endpoint errors are derived from the proved curvature estimates. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT

namespace FaceSmoother

theorem integral_indicator_eq_probability
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsFiniteMeasure μ] (W : Ω → Vector p) (hW : Measurable W) :
    (∫ ω, s.indicator (W ω) ∂μ) = μ.real {ω | s.Inside (W ω)} := by
  classical
  have hs : MeasurableSet {ω | s.Inside (W ω)} := s.measurableSet_Inside.preimage hW
  have heq : (fun ω => s.indicator (W ω)) =
      {ω | s.Inside (W ω)}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [indicator, Set.indicator, mem_setOf_eq]
  rw [heq, integral_indicator_const (1 : ℝ) hs]
  simp

theorem integral_endpoint_error_le_kappa
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsFiniteMeasure μ] (W : Ω → Vector p) (hW : Measurable W) :
    |(∫ ω, s.F (W ω) ∂μ) - μ.real {ω | s.Inside (W ω)}| ≤
      2 * (∫ ω, s.kappa (W ω) ∂μ) := by
  classical
  have hs : MeasurableSet {ω | s.Inside (W ω)} := s.measurableSet_Inside.preimage hW
  have hI : Integrable (fun ω => s.indicator (W ω)) μ := by
    have hh := (integrable_const (1 : ℝ) (μ := μ)).indicator hs
    simpa only [indicator, Set.indicator, mem_setOf_eq] using hh
  have hF : Integrable (fun ω => s.F (W ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (s.continuous_F.measurable.comp hW).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => s.norm_F_le_one _
  rw [← s.integral_indicator_eq_probability μ W hW, ← integral_sub hF hI]
  have hnorm := norm_integral_le_integral_norm (μ := μ)
    (fun ω => s.F (W ω) - s.indicator (W ω))
  rw [Real.norm_eq_abs] at hnorm
  have hh := integral_mono (hF.sub hI).norm ((s.integrable_kappa hW).const_mul 2)
    (fun ω => by simpa only [Real.norm_eq_abs] using s.endpoint_error (W ω))
  rw [integral_const_mul] at hh
  exact hnorm.trans hh

theorem probability_gap_le_smoother_gap_add_kappa
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure E) [IsFiniteMeasure ν]
    (W : Ω → Vector p) (hW : Measurable W) (Z : E → Vector p) (hZ : Measurable Z) :
    |μ.real {ω | s.Inside (W ω)} - ν.real {z | s.Inside (Z z)}| ≤
      |(∫ ω, s.F (W ω) ∂μ) - (∫ z, s.F (Z z) ∂ν)| +
        2 * ((∫ ω, s.kappa (W ω) ∂μ) + (∫ z, s.kappa (Z z) ∂ν)) := by
  have hμ := s.integral_endpoint_error_le_kappa μ W hW
  have hν := s.integral_endpoint_error_le_kappa ν Z hZ
  have hm := abs_le.mp (le_refl |(∫ ω, s.F (W ω) ∂μ) - (∫ z, s.F (Z z) ∂ν)|)
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hμ).1, (abs_le.mp hμ).2,
    (abs_le.mp hν).1, (abs_le.mp hν).2, hm.1, hm.2]

noncomputable def closedBox (lo hi : Vector p) (h : ℝ) (hh : 0 < h) : FaceSmoother p where
  faces := Finset.univ
  offsets f := if f.2 then hi f.1 else -lo f.1
  bandwidth := h
  bandwidth_pos := hh

theorem closedBox_Inside (lo hi : Vector p) (h : ℝ) (hh : 0 < h) (x : Vector p) :
    (closedBox lo hi h hh).Inside x ↔ x ∈ (Rect.closedBox lo hi).carrier := by
  simp only [Inside, faceScore, closedBox, Finset.mem_univ, forall_true_left,
    Rect.carrier, Rect.closedBox, mem_pi, mem_univ, mem_Icc]
  constructor
  · intro hx j
    have hlo := hx (j, false)
    have hhi := hx (j, true)
    simp only [normalDot, Bool.false_eq_true, ↓reduceIte] at hlo hhi
    constructor <;> linarith
  · intro hx f
    have hj := hx f.1
    rcases f with ⟨j, b⟩
    cases b <;> simp only [normalDot, Bool.false_eq_true, ↓reduceIte] <;> linarith

end FaceSmoother

namespace BoundedIndependentHypotheses

theorem smoother_rectangle_error_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (sumVector ξ))
    (hc : 0 < pairGap (covariance μ (sumVector ξ)))
    (s : FaceSmoother p) (hband : δ ≤ s.bandwidth) :
    |μ.real {ω | s.Inside (sumVector ξ ω)} - (gaussianLaw A).real {z | s.Inside z}| ≤
      |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| +
        (8 * Real.exp 4 + 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
          pairGap (covariance μ (sumVector ξ)) := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => h.measurable i)
  have hh := s.probability_gap_le_smoother_gap_add_kappa μ (gaussianLaw A)
    (sumVector ξ) hW id measurable_id
  have hb := h.integral_kappa_le s 0 hp hunit hc hband
  simp only [add_zero] at hb
  have hg := s.gaussian_expected_kappa_le hp A 0
    (fun j => by rw [hfactor]; exact hunit j) (by rw [hfactor]; exact hc)
  simp only [add_zero, hfactor] at hg
  dsimp only [id_eq] at hh
  have heq : 2 * ((4 * Real.exp 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
      pairGap (covariance μ (sumVector ξ)) +
      2 * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap (covariance μ (sumVector ξ))) =
      (8 * Real.exp 4 + 4) * s.bandwidth * Real.sqrt (dimensionLog p) /
        pairGap (covariance μ (sumVector ξ)) := by ring
  rw [← heq]
  linarith

theorem closedBox_error_le_smoother_gap
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ h : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (sumVector ξ))
    (hc : 0 < pairGap (covariance μ (sumVector ξ)))
    (lo hi : Vector p) (hh : 0 < h) (hband : δ ≤ h) :
    rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
      |(∫ ω, (FaceSmoother.closedBox lo hi h hh).F (sumVector ξ ω) ∂μ) -
        (∫ z, (FaceSmoother.closedBox lo hi h hh).F z ∂gaussianLaw A)| +
      (8 * Real.exp 4 + 4) * h * Real.sqrt (dimensionLog p) /
        pairGap (covariance μ (sumVector ξ)) := by
  have hh' := hdata.smoother_rectangle_error_le hp hunit A hfactor hc
    (FaceSmoother.closedBox lo hi h hh) hband
  have hμ : {ω | (FaceSmoother.closedBox lo hi h hh).Inside (sumVector ξ ω)} =
      sumVector ξ ⁻¹' (Rect.closedBox lo hi).carrier := by
    ext ω
    exact FaceSmoother.closedBox_Inside lo hi h hh (sumVector ξ ω)
  have hG : {z | (FaceSmoother.closedBox lo hi h hh).Inside z} =
      (Rect.closedBox lo hi).carrier := by
    ext z
    exact FaceSmoother.closedBox_Inside lo hi h hh z
  rw [hμ, hG] at hh'
  simpa only [rectangleError, FaceSmoother.closedBox] using hh'

end BoundedIndependentHypotheses

end RectangleCLT

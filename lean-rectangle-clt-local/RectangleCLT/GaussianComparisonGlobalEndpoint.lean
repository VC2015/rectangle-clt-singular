import RectangleCLT.GaussianComparisonLocal
import RectangleCLT.GaussianEnvelope

/-! Gap-free endpoint approximation for Gaussian comparison. The auxiliary
dimension factor disappears with the bandwidth and does not enter the final
comparison constant. No gap assumption is imposed on either endpoint here. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem FaceWeights.error_inside_le_smallerEnvelope {p : ℕ} (w : FaceWeights p)
    (hw : ∀ f, w.weight f ≤ 1) :
    |w.F - 1| ≤ ((Fintype.card (Face p) : ℝ) + 2) * (w.F * (1 - w.F)) := by
  have hT : w.T ≤ (Fintype.card (Face p) : ℝ) := by
    calc
      w.T ≤ ∑ _f : Face p, (1 : ℝ) := Finset.sum_le_sum fun f _ => hw f
      _ = _ := by simp
  have hcoeff : 1 ≤ ((Fintype.card (Face p) : ℝ) + 2) * w.F := by
    rw [FaceWeights.F, mul_one_div]
    apply (le_div_iff₀ w.denominator_pos).mpr
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr w.F_le_one)]
  have hh := mul_le_mul_of_nonneg_right hcoeff (sub_nonneg.mpr w.F_le_one)
  nlinarith

theorem FaceWeights.error_outside_le_smallerEnvelope {p : ℕ} (w : FaceWeights p)
    (hT : 1 ≤ w.T) :
    |w.F| ≤ ((Fintype.card (Face p) : ℝ) + 2) * (w.F * (1 - w.F)) := by
  have ht := w.half_le_theta_of_one_le_T hT
  have hc : (2 : ℝ) ≤ (Fintype.card (Face p) : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ Fintype.card (Face p) := Nat.cast_nonneg _
    linarith
  have hnon : 0 ≤ 1 - w.F := sub_nonneg.mpr w.F_le_one
  have hh := mul_le_mul_of_nonneg_right hc hnon
  rw [abs_of_pos w.F_pos]
  unfold FaceWeights.theta at ht
  nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤
    ((Fintype.card (Face p) : ℝ) + 2) * (1 - w.F) by linarith) w.F_pos.le]

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem endpoint_error_le_smallerEnvelope (x : Vector p) :
    |s.F x - s.indicator x| ≤ ((Fintype.card (Face p) : ℝ) + 2) *
      (s.F x * (1 - s.F x)) := by
  classical
  by_cases hx : s.Inside x
  · simpa only [F, indicator, if_pos hx] using
      (s.weights x).error_inside_le_smallerEnvelope (s.inside_weights_le_one x hx)
  · simpa only [F, indicator, if_neg hx, sub_zero] using
      (s.weights x).error_outside_le_smallerEnvelope (s.outside_one_lt_T x hx).le

theorem integral_endpoint_error_le_smallerEnvelope
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) :
    |(∫ ω, s.F (W ω) ∂μ) - μ.real {ω | s.Inside (W ω)}| ≤
      ((Fintype.card (Face p) : ℝ) + 2) *
        (∫ ω, s.F (W ω) * (1 - s.F (W ω)) ∂μ) := by
  classical
  have hs : MeasurableSet {ω | s.Inside (W ω)} := s.measurableSet_Inside.preimage hW
  have hI : Integrable (fun ω => s.indicator (W ω)) μ := by
    simpa only [indicator, Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ) (μ := μ)).indicator hs
  have hF : Integrable (fun ω => s.F (W ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (s.continuous_F.measurable.comp hW).aestronglyMeasurable
    exact ae_of_all _ fun ω => s.norm_F_le_one _
  rw [← s.integral_indicator_eq_probability μ W hW, ← integral_sub hF hI]
  have hh := norm_integral_le_integral_norm (μ := μ)
    (fun ω => s.F (W ω) - s.indicator (W ω))
  rw [Real.norm_eq_abs] at hh
  have hm := integral_mono (hF.sub hI).norm
    ((s.integrable_smallerEnvelope W hW).const_mul ((Fintype.card (Face p) : ℝ) + 2))
    (fun ω => by simpa only [Real.norm_eq_abs] using s.endpoint_error_le_smallerEnvelope (W ω))
  rw [integral_const_mul] at hm
  exact hh.trans hm

/-- Gaussian endpoint approximation for possibly singular covariance, with
no local nondegeneracy assumption. -/
theorem gaussian_integral_endpoint_error_le_gap_free (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : ∀ j, (A * A.transpose) j j = 1) :
    |(∫ x, s.F x ∂gaussianLaw A) - (gaussianLaw A).real {x | s.Inside x}| ≤
      ((Fintype.card (Face p) : ℝ) + 2) * Real.exp (3 / 2 : ℝ) *
        s.bandwidth * Real.sqrt (dimensionLog p) := by
  have hh := s.integral_endpoint_error_le_smallerEnvelope (gaussianLaw A) id measurable_id
  have hg := s.gaussian_expected_variance_le_of_diagonal hp A
    (by norm_num : (0 : ℝ) < 1) hA 0
  simp only [add_zero, div_one, id_eq] at hh hg
  exact hh.trans ((mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (by ring))

end FaceSmoother

end

end RectangleCLT

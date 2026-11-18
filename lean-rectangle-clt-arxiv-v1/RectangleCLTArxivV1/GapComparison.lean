import RectangleCLTArxivV1.GapIntegration
import RectangleCLTArxivV1.SupplementalGCapComparison

/-! FTC and the literal finite crossing-time integration for Appendix H.
The actual derivative and its early/late estimates remain explicit
inputs of the scalar comparison, as required at this intermediate stage. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set
open scoped Interval
noncomputable section
set_option autoImplicit false

def positiveGapMajorant (A ε C c v : ℝ) : ℝ :=
  C*min (A/v) ((A*Real.sqrt ε/exceptionalCutoffDet c)/(v*Real.sqrt v))

theorem positiveGapMajorant_nonneg {A ε C c v : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1) (hv : 0 < v) :
    0 ≤ positiveGapMajorant A ε C c v := by
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  unfold positiveGapMajorant
  positivity

theorem positiveGapMajorant_continuousOn {a b A ε C c : ℝ} (ha : 0 < a) :
    ContinuousOn (positiveGapMajorant A ε C c) (Icc a b) :=
  continuousOn_const.mul ((cap_const_inv_continuousOn ha A).inf
    (cap_const_inv_mul_sqrt_continuousOn ha (A*Real.sqrt ε/exceptionalCutoffDet c)))

theorem positiveGap_integral_majorant_bound {ε A C c : ℝ}
    (hε : 0 < ε) (hA : 0 < A) (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ t in (0:ℝ)..1, positiveGapMajorant A ε C c (t+ε)) ≤
      2*C*A*positiveGapGain c := by
  have hd := exceptionalCutoffDet_bounds hc hc1
  have hm := positiveGap_integral_minimum hε (by linarith : ε≤1+ε) hA hd.1 hd.2.2
  have hg := positiveGapGain_det_le hc hc1
  rw [intervalIntegral.integral_comp_add_right,zero_add]
  unfold positiveGapMajorant
  rw [intervalIntegral.integral_const_mul]
  calc
    _ ≤ C*(2*A*positiveGapGain (exceptionalCutoffDet c)) := mul_le_mul_of_nonneg_left hm hC
    _ ≤ C*(2*A*positiveGapGain c) := by gcongr
    _ = _ := by ring

/-- A continuous expectation curve and its actual derivative can be
integrated without assuming integrability of that derivative. -/
theorem positiveGap_time_increment_bound {P D : ℝ → ℝ} {a ε A C c : ℝ}
    (hε : 0 < ε) (hA : 0 < A) (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (hP : ContinuousOn P (Icc (0:ℝ) 1))
    (hD : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt P (D t) t)
    (hearly : ∀ t ∈ Ioo (0:ℝ) 1, |D t| ≤ a+C*(A/(t+ε)))
    (hlate : ∀ t ∈ Ioo (0:ℝ) 1, |D t| ≤
      a+C*((A*Real.sqrt ε/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε)))) :
    |P 1-P 0| ≤ a+2*C*A*positiveGapGain c := by
  let M := fun t => positiveGapMajorant A ε C c (t+ε)
  have hM : ContinuousOn M (Icc (0:ℝ) 1) :=
    (positiveGapMajorant_continuousOn (b := 1+ε) hε).comp
      (continuousOn_id.add continuousOn_const)
      (fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hb (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : |D t| ≤ a+M t := by
    dsimp only [M,positiveGapMajorant]
    rw [mul_min_of_nonneg _ _ hC,add_min]
    exact le_min (hearly t ht) (hlate t ht)
  exact (cap_time_increment_le hP hD hM hb).trans
    (add_le_add_left (positiveGap_integral_majorant_bound hε hA hC hc hc1) a)

end
end RectangleCLTArxivV1

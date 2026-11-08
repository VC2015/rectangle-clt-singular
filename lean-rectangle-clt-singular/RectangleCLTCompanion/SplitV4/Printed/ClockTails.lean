import RectangleCLT.ExponentialMixture
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The literal single-clock tail in the printed endpoint argument.
All measures are the actual product exponential measures used by the
logistic random-threshold representation. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem face_coordinate_real {p : ℕ} (f : Face p) (S : Set ℝ) :
    (faceExponentialLaw p).real {e | e f ∈ S} = unitExponential.real S := by
  classical
  have he : {e : Face p → ℝ | e f ∈ S} =
      Set.pi Set.univ (fun j => if j = f then S else Set.univ) := by
    ext e
    simp only [mem_setOf_eq, mem_pi, mem_univ, forall_true_left]
    constructor
    · intro h j
      split_ifs with hj
      · simpa only [hj] using h
      · trivial
    · intro h
      simpa using h f
  rw [he, measureReal_def, faceExponentialLaw, Measure.pi_pi]
  simp [apply_ite, measureReal_def]

theorem face_coordinate_measurePreserving {p : ℕ} (f : Face p) :
    MeasurePreserving (fun e : Face p → ℝ => e f) (faceExponentialLaw p) unitExponential := by
  refine ⟨measurable_pi_apply f, ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_pi_apply f) hS]
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact face_coordinate_real f S

theorem clock_pair_measurePreserving {p : ℕ} (f : Face p) :
    MeasurePreserving (fun e : ℝ × (Face p → ℝ) => (e.1,e.2 f))
      (exponentialRectangleLaw p) (unitExponential.prod unitExponential) := by
  exact (MeasurePreserving.id unitExponential).prod (face_coordinate_measurePreserving f)

theorem exponential_pair_upper_tail {c : ℝ} (hc : 0 ≤ c) :
    (unitExponential.prod unitExponential).real {z : ℝ × ℝ | c*z.1 < z.2} = 1/(1+c) := by
  let S : Set (ℝ × ℝ) := {z | c*z.1 < z.2}
  have hS : MeasurableSet S := measurableSet_lt (measurable_const.mul measurable_fst) measurable_snd
  have hi : Integrable (S.indicator (fun _ => (1 : ℝ)))
      (unitExponential.prod unitExponential) := (integrable_const _).indicator hS
  calc
    _ = ∫ z, S.indicator (fun _ => (1 : ℝ)) z ∂unitExponential.prod unitExponential :=
      (integral_indicator_one hS).symm
    _ = ∫ x, ∫ y, S.indicator (fun _ => (1 : ℝ)) (x,y) ∂unitExponential ∂unitExponential :=
      integral_prod _ hi
    _ = ∫ x, Real.exp (-c*x) ∂unitExponential := by
      apply integral_congr_ae
      filter_upwards [unitExponential_ae_pos] with x hx
      change (∫ y, (Ioi (c*x)).indicator (fun _ => (1 : ℝ)) y ∂unitExponential) = _
      rw [integral_indicator_const (1 : ℝ) measurableSet_Ioi, smul_eq_mul, mul_one,
        unitExponential_Ioi (mul_nonneg hc hx.le)]
      congr 1
      ring
    _ = _ := unitExponential_laplace hc

theorem exponential_pair_lower_tail {c : ℝ} (hc : 0 ≤ c) :
    (unitExponential.prod unitExponential).real {z : ℝ × ℝ | c*z.2 < z.1} = 1/(1+c) := by
  have hS : MeasurableSet {z : ℝ × ℝ | c*z.1 < z.2} :=
    measurableSet_lt (measurable_const.mul measurable_fst) measurable_snd
  have hm := (Measure.measurePreserving_swap (μ := unitExponential) (ν := unitExponential)).measure_preimage
    hS.nullMeasurableSet
  have hr := congrArg ENNReal.toReal hm
  exact hr.trans (exponential_pair_upper_tail hc)

theorem exponential_pair_abs_log_ratio_tail {s : ℝ} (hs : 0 ≤ s) :
    (unitExponential.prod unitExponential).real
      {z : ℝ × ℝ | s < |Real.log (z.2/z.1)|} = 2/(1+Real.exp s) := by
  let c := Real.exp s
  let U : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2 ∧ c*z.1 < z.2}
  let V : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2 ∧ c*z.2 < z.1}
  have hc : 1 ≤ c := Real.one_le_exp hs
  have hpos : ∀ᵐ z : ℝ × ℝ ∂unitExponential.prod unitExponential, 0 < z.1 ∧ 0 < z.2 :=
    (Measure.quasiMeasurePreserving_fst.ae unitExponential_ae_pos).and
      (Measure.quasiMeasurePreserving_snd.ae unitExponential_ae_pos)
  have hU : MeasurableSet U := (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (measurable_const.mul measurable_fst) measurable_snd))
  have hV : MeasurableSet V := (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (measurable_const.mul measurable_snd) measurable_fst))
  have hdis : Disjoint U V := by
    apply disjoint_left.mpr
    intro z hz hv
    have hcx := mul_le_mul_of_nonneg_right hc hz.1.le
    have hcy := mul_le_mul_of_nonneg_right hc hz.2.1.le
    dsimp [U,V] at hz hv
    nlinarith [hz.2.2,hv.2.2]
  have hlog (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
      s < |Real.log (y/x)| ↔ c*x < y ∨ c*y < x := by
    rw [lt_abs]
    have hupper : s < Real.log (y/x) ↔ c*x < y := by
      rw [Real.lt_log_iff_exp_lt (div_pos hy hx), lt_div_iff₀ hx]
    have hlower : s < -Real.log (y/x) ↔ c*y < x := by
      rw [← Real.log_inv, inv_div, Real.lt_log_iff_exp_lt (div_pos hx hy), lt_div_iff₀ hy]
    exact or_congr hupper hlower
  have hset : {z : ℝ × ℝ | s < |Real.log (z.2/z.1)|} =ᵐ[unitExponential.prod unitExponential] (U ∪ V : Set (ℝ × ℝ)) := by
    filter_upwards [hpos] with z hz
    change (s < |Real.log (z.2/z.1)|) = ((0<z.1 ∧ 0<z.2 ∧ c*z.1<z.2) ∨ (0<z.1 ∧ 0<z.2 ∧ c*z.2<z.1))
    simp only [hz.1,hz.2,true_and]
    exact propext (hlog z.1 z.2 hz.1 hz.2)
  have hu : (unitExponential.prod unitExponential).real U = 1/(1+c) := by
    rw [← exponential_pair_upper_tail (le_trans zero_le_one hc)]
    apply measureReal_congr
    filter_upwards [hpos] with z hz
    change (0<z.1 ∧ 0<z.2 ∧ c*z.1<z.2) = (c*z.1<z.2)
    simp only [hz.1,hz.2,true_and]
  have hv : (unitExponential.prod unitExponential).real V = 1/(1+c) := by
    rw [← exponential_pair_lower_tail (le_trans zero_le_one hc)]
    apply measureReal_congr
    filter_upwards [hpos] with z hz
    change (0<z.1 ∧ 0<z.2 ∧ c*z.2<z.1) = (c*z.2<z.1)
    simp only [hz.1,hz.2,true_and]
  rw [measureReal_congr hset, measureReal_union hdis hV, hu,hv]
  dsimp [c]
  ring

theorem clock_abs_log_ratio_tail {p : ℕ} (f : Face p) {s : ℝ} (hs : 0 ≤ s) :
    (exponentialRectangleLaw p).real
      {e | s < |Real.log (e.2 f/e.1)|} = 2/(1+Real.exp s) := by
  have hS : MeasurableSet {z : ℝ × ℝ | s < |Real.log (z.2/z.1)|} :=
    measurableSet_lt measurable_const ((measurable_snd.div measurable_fst).log.abs)
  have hm := (clock_pair_measurePreserving f).measure_preimage hS.nullMeasurableSet
  have hr := congrArg ENNReal.toReal hm
  exact hr.trans (exponential_pair_abs_log_ratio_tail hs)

theorem clock_abs_log_ratio_tail_le {p : ℕ} (f : Face p) {s : ℝ} (hs : 0 ≤ s) :
    (exponentialRectangleLaw p).real
      {e | s < |Real.log (e.2 f/e.1)|} ≤ 2*Real.exp (-s) := by
  rw [clock_abs_log_ratio_tail f hs, Real.exp_neg]
  have he : 0 < Real.exp s := Real.exp_pos s
  simpa only [div_eq_mul_inv] using
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) he (by linarith : Real.exp s ≤ 1+Real.exp s))

end
end RectangleCLT.Companion.SplitV4.Printed

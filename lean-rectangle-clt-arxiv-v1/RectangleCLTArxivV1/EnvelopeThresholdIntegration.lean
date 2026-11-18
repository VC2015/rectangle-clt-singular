import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAllOrders
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Complex.ExponentialBounds

/-! The common-threshold differential and integration argument in A.1. -/

namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped Interval
noncomputable section
set_option autoImplicit false

theorem exp_one_le_four : Real.exp 1 ≤ 4 :=
  Real.exp_one_lt_d9.le.trans (by norm_num)

def thresholdLogistic (T h s : ℝ) : ℝ := 1 / (1+Real.exp (-s/h)*T)

def thresholdEnvelope (T h s : ℝ) : ℝ :=
  thresholdLogistic T h s*(1-thresholdLogistic T h s)

theorem thresholdLogistic_pos {T h : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    0 < thresholdLogistic T h s := by unfold thresholdLogistic; positivity

theorem thresholdLogistic_le_one {T h : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    thresholdLogistic T h s ≤ 1 := by
  unfold thresholdLogistic
  apply (div_le_one (by positivity)).mpr
  nlinarith [mul_nonneg (Real.exp_nonneg (-s/h)) hT]

theorem thresholdEnvelope_pos {T h : ℝ} (hT : 0 < T) (s : ℝ) :
    0 < thresholdEnvelope T h s := by
  have hf : thresholdLogistic T h s < 1 := by
    unfold thresholdLogistic
    apply (div_lt_one (by positivity)).mpr
    nlinarith [mul_pos (Real.exp_pos (-s/h)) hT]
  exact mul_pos (thresholdLogistic_pos hT.le s) (sub_pos.mpr hf)

theorem hasDerivAt_thresholdLogistic {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (s : ℝ) :
    HasDerivAt (thresholdLogistic T h) (h⁻¹*thresholdEnvelope T h s) s := by
  have hden : 1+Real.exp (-s/h)*T ≠ 0 := by positivity
  have hd := (hasDerivAt_const s (1:ℝ)).div
    (((((hasDerivAt_id s).neg.div_const h).exp).mul_const T).const_add 1) hden
  convert hd using 1
  unfold thresholdEnvelope thresholdLogistic
  field_simp [hden,hh.ne']
  ring
  all_goals simp

theorem hasDerivAt_log_thresholdEnvelope {T h : ℝ} (hT : 0 < T) (hh : 0 < h) (s : ℝ) :
    HasDerivAt (fun t => Real.log (thresholdEnvelope T h t))
      (h⁻¹*(1-2*thresholdLogistic T h s)) s := by
  have hd := hasDerivAt_thresholdLogistic hT.le hh s
  have he : thresholdEnvelope T h s ≠ 0 := ne_of_gt (thresholdEnvelope_pos hT s)
  have hb := (hd.mul ((hasDerivAt_const s (1:ℝ)).sub hd)).log he
  have hcoef : h⁻¹*(1-2*thresholdLogistic T h s) =
      ((h⁻¹*thresholdEnvelope T h s)*(1-thresholdLogistic T h s)+
        thresholdLogistic T h s*(0-h⁻¹*thresholdEnvelope T h s))/thresholdEnvelope T h s := by
    field_simp [he]
    ring
  rw [hcoef]
  exact hb

theorem abs_log_thresholdEnvelope_derivative {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (s : ℝ) :
    |h⁻¹*(1-2*thresholdLogistic T h s)| ≤ h⁻¹ := by
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hh.le)]
  have hb : |1-2*thresholdLogistic T h s| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [thresholdLogistic_pos (h := h) hT s,thresholdLogistic_le_one (h := h) hT s]
  simpa using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)

/-- Integrating the logarithmic derivative bound from zero to `s` controls
the envelope on the entire interval of common threshold shifts. -/
theorem thresholdEnvelope_lower_on_interval {T h : ℝ} (hT : 0 < T) (hh : 0 < h)
    {s : ℝ} (hs : |s| ≤ h) :
    Real.exp (-1)*thresholdEnvelope T h 0 ≤ thresholdEnvelope T h s := by
  have hcont : Continuous (thresholdLogistic T h) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_thresholdLogistic hT.le hh t).continuousAt)
  have hci : IntervalIntegrable (fun t => h⁻¹*(1-2*thresholdLogistic T h t)) volume 0 s :=
    (continuous_const.mul (continuous_const.sub (continuous_const.mul hcont))).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := s) (fun t _ => hasDerivAt_log_thresholdEnvelope hT hh t) hci
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (C := h⁻¹) (f := fun t => h⁻¹*(1-2*thresholdLogistic T h t))
    (fun t _ => by
      simpa only [Real.norm_eq_abs] using abs_log_thresholdEnvelope_derivative hT.le hh t)
  rw [hftc] at hb
  simp only [Real.norm_eq_abs,sub_zero] at hb
  have hlen : h⁻¹*|s| ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hh.le)
    simpa only [inv_mul_cancel₀ hh.ne'] using hm
  have hlog : Real.log (thresholdEnvelope T h 0)-1 ≤ Real.log (thresholdEnvelope T h s) := by
    have hl := (abs_le.mp (hb.trans hlen)).1
    linarith only [hl]
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub,Real.exp_log (thresholdEnvelope_pos hT 0),
    Real.exp_log (thresholdEnvelope_pos hT s)] at he
  simpa only [Real.exp_neg,div_eq_mul_inv,mul_comm] using he

/-- The second integration in the printed proof, now over `[-h,h]`,
gives its exact pointwise comparison with coefficient `e/2`. -/
theorem thresholdEnvelope_le_common_threshold_difference {T h : ℝ}
    (hT : 0 ≤ T) (hh : 0 < h) :
    thresholdEnvelope T h 0 ≤ Real.exp 1/2*
      (thresholdLogistic T h h-thresholdLogistic T h (-h)) := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    simp [thresholdEnvelope,thresholdLogistic]
  have hcont : Continuous (thresholdLogistic T h) :=
    continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_thresholdLogistic hT.le hh s).continuousAt)
  have hci : IntervalIntegrable (fun s => h⁻¹*thresholdEnvelope T h s) volume (-h) h := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (hcont.mul (continuous_const.sub hcont))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -h) (b := h) (fun s _ => hasDerivAt_thresholdLogistic hT.le hh s) hci
  have hlow := intervalIntegral.integral_mono_on (by linarith : -h≤h)
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => h⁻¹*(Real.exp (-1)*thresholdEnvelope T h 0)) volume (-h) h) hci
    (fun s hs => mul_le_mul_of_nonneg_left
      (thresholdEnvelope_lower_on_interval hT hh (abs_le.mpr hs)) (inv_nonneg.mpr hh.le))
  rw [hftc,intervalIntegral.integral_const] at hlow
  simp only [smul_eq_mul] at hlow
  have hc : (h- -h)*(h⁻¹*(Real.exp (-1)*thresholdEnvelope T h 0)) =
      2*Real.exp (-1)*thresholdEnvelope T h 0 := by field_simp; ring
  rw [hc] at hlow
  have hm := mul_le_mul_of_nonneg_left hlow (Real.exp_nonneg 1)
  have he : Real.exp 1*Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hcancel : Real.exp 1*(2*Real.exp (-1)*thresholdEnvelope T h 0) =
      2*thresholdEnvelope T h 0 := by
    calc
      _ = 2*(Real.exp 1*Real.exp (-1))*thresholdEnvelope T h 0 := by ring
      _ = _ := by rw [he]; ring
  rw [hcancel] at hm
  nlinarith only [hm,he]


/-- The exact pointwise comparison `F(1-F) ≤ (e/2)(F_h-F_-h)`
for a genuine finite-face smoother. -/
theorem smallerEnvelope_le_threshold_integral {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    s.F x*(1-s.F x) ≤ Real.exp 1/2*
      ((s.shiftOffsets s.bandwidth).F x-(s.shiftOffsets (-s.bandwidth)).F x) := by
  have hh := thresholdEnvelope_le_common_threshold_difference (s.weights x).T_nonneg s.bandwidth_pos
  rw [s.shiftOffsets_F,s.shiftOffsets_F]
  simpa only [thresholdEnvelope,thresholdLogistic,neg_zero,zero_div,Real.exp_zero,one_mul,
    FaceSmoother.F,FaceWeights.F] using hh

theorem integral_smallerEnvelope_le_of_matching_boundary_printed {p : ℕ} (s : FaceSmoother p)
    (μ : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ] {M : ℝ}
    (hboundary : ∀ r : FaceSmoother p, r.faces = s.faces →
      μ.real {x | (∀ f ∈ r.faces, r.faceScore f x ≤ s.bandwidth) ∧
        ¬(∀ f ∈ r.faces, r.faceScore f x ≤ -(s.bandwidth))} ≤ M) :
    (∫ x, s.F x * (1 - s.F x) ∂μ) ≤ (Real.exp 1/2) * M := by
  let a := s.bandwidth
  have ha : 0 ≤ a := s.bandwidth_pos.le
  have hiF (r : FaceSmoother p) : Integrable r.F μ := by
    apply (integrable_const (1 : ℝ)).mono' r.continuous_F.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall r.norm_F_le_one
  have hiEnv : Integrable (fun x => s.F x * (1 - s.F x)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (s.continuous_F.mul (continuous_const.sub s.continuous_F)).measurable.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (s.F_pos x).le (by linarith [s.F_le_one x]))]
    nlinarith [s.F_le_one x, sq_nonneg (s.F x)]
  have hiDiff : Integrable
      (fun x => (Real.exp 1/2) * ((s.shiftOffsets a).F x - (s.shiftOffsets (-a)).F x)) μ :=
    (((hiF (s.shiftOffsets a)).sub (hiF (s.shiftOffsets (-a)))).const_mul (Real.exp 1/2))
  have hpoint := integral_mono_ae hiEnv hiDiff
    (Filter.Eventually.of_forall fun x => by
      simpa only [a] using smallerEnvelope_le_threshold_integral s x)
  have heq : (∫ x, (Real.exp 1/2) * ((s.shiftOffsets a).F x - (s.shiftOffsets (-a)).F x) ∂μ) =
      (Real.exp 1/2) * ∫ e, (μ.real {x | ((s.shiftOffsets a).randomRectangle e).Inside x} -
        μ.real {x | ((s.shiftOffsets (-a)).randomRectangle e).Inside x})
        ∂exponentialRectangleLaw p := by
    rw [integral_const_mul, integral_sub (hiF _) (hiF _),
      FaceSmoother.integral_F_eq_randomRectangle_average, FaceSmoother.integral_F_eq_randomRectangle_average,
      integral_sub ((s.shiftOffsets a).integrable_randomRectangle_probability μ)
        ((s.shiftOffsets (-a)).integrable_randomRectangle_probability μ)]
  rw [heq] at hpoint
  have hbound : ∀ e : ℝ × (Face p → ℝ),
      μ.real {x | ((s.shiftOffsets a).randomRectangle e).Inside x} -
        μ.real {x | ((s.shiftOffsets (-a)).randomRectangle e).Inside x} ≤ M := by
    intro e
    simp only [FaceSmoother.shiftOffsets_randomRectangle]
    have hsub : {x | ((s.randomRectangle e).shiftOffsets (-a)).Inside x} ⊆
        {x | ((s.randomRectangle e).shiftOffsets a).Inside x} := by
      intro x hx
      simp only [mem_setOf_eq] at hx ⊢
      rw [FaceSmoother.shiftOffsets_Inside_iff] at hx ⊢
      intro f hf
      exact (hx f hf).trans (by linarith)
    rw [← measureReal_diff hsub ((s.randomRectangle e).shiftOffsets (-a)).measurableSet_Inside]
    have hset : {x | ((s.randomRectangle e).shiftOffsets a).Inside x} \
        {x | ((s.randomRectangle e).shiftOffsets (-a)).Inside x} =
        {x | (∀ f ∈ (s.randomRectangle e).faces, (s.randomRectangle e).faceScore f x ≤ a) ∧
          ¬(∀ f ∈ (s.randomRectangle e).faces, (s.randomRectangle e).faceScore f x ≤ -a)} := by
      ext x
      simp only [mem_diff, mem_setOf_eq, FaceSmoother.shiftOffsets_Inside_iff]
    rw [hset]
    exact hboundary (s.randomRectangle e) rfl
  have hh := integral_mono_ae
    (((s.shiftOffsets a).integrable_randomRectangle_probability μ).sub
      ((s.shiftOffsets (-a)).integrable_randomRectangle_probability μ))
    (integrable_const M) (Filter.Eventually.of_forall hbound)
  simp only [Pi.sub_apply, integral_const, measureReal_univ_eq_one, one_smul] at hh
  exact hpoint.trans (mul_le_mul_of_nonneg_left hh (by positivity))

theorem integral_logisticEnvelope_le_of_layer_bound_printed
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Vector r) (hX : Measurable X)
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h M : ℝ} (hh : 0 < h)
    (hboundary : ∀ b : Vector m,
      μ.real {ω | X ω ∈ gaussianPolyhedronLayer U b (h)} ≤ M) :
    (∫ ω, logisticNullWeight U a h (X ω)*(1-logisticNullWeight U a h (X ω)) ∂μ) ≤ (Real.exp 1/2)*M := by
  let s := upperFaceSmoother a h hh
  let Z : Ω → Vector m := fun ω => U.mulVec (X ω)
  have hZ : Measurable Z := (measurable_rectangular_mulVec U).comp hX
  let ν := μ.map Z
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_map hZ.aemeasurable
  have hb : (∫ y, s.F y*(1-s.F y) ∂ν) ≤ (Real.exp 1/2)*M := by
    apply integral_smallerEnvelope_le_of_matching_boundary_printed s ν
    intro q hq
    have hm (c : ℝ) : MeasurableSet {y : Vector m | ∀ f ∈ q.faces, q.faceScore f y ≤ c} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
        measurableSet_le (q.continuous_faceScore f).measurable measurable_const))
    have hmS : MeasurableSet {y : Vector m |
        (∀ f ∈ q.faces, q.faceScore f y ≤ s.bandwidth) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f y ≤ -(s.bandwidth))} :=
      (hm _).inter (hm _).compl
    have hmap := map_measureReal_apply (μ := μ) hZ hmS
    rw [hmap]
    have hevent : {ω : Ω |
        (∀ f ∈ q.faces, q.faceScore f (Z ω) ≤ s.bandwidth) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f (Z ω) ≤ -(s.bandwidth))} =
        {ω : Ω | X ω ∈ gaussianPolyhedronLayer U (fun j => q.offsets (j, true)) (h)} := by
      ext ω
      change ((∀ f ∈ q.faces, q.faceScore f (U.mulVec (X ω)) ≤ h) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f (U.mulVec (X ω)) ≤ -(h))) ↔ _
      rw [upperFaceSmoother_face_scores_iff U a hh q hq, upperFaceSmoother_face_scores_iff U a hh q hq]
      simp only [gaussianPolyhedronLayer, RectangleCLT.Companion.SplitV4.facePolyhedron, Set.mem_diff, Set.mem_setOf_eq,
        sub_eq_add_neg, faceDot, dotProduct]
    exact (congrArg (fun S => μ.real S) hevent).le.trans (hboundary _)
  have hf : Continuous (fun y : Vector m => s.F y*(1-s.F y)) :=
    s.continuous_F.mul (continuous_const.sub s.continuous_F)
  have hmap := integral_map (μ := μ) hZ.aemeasurable hf.aestronglyMeasurable
  rw [hmap] at hb
  simpa only [Z, s, Function.comp_apply, upperFaceSmoother_F] using hb

end
end RectangleCLTArxivV1

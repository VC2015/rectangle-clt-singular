import RectangleCLT.EnvelopeAveraging
import RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate
import RectangleCLTCompanion.SplitV4.Concentration

/-! Genuine smaller-envelope averaging for arbitrary finite face normals.
Only the active upper faces enter the boundary hypothesis; the independent
component estimates later discharge that actual probability bound. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem integral_smallerEnvelope_le_of_matching_boundary {p : ℕ} (s : FaceSmoother p)
    (μ : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ] {M : ℝ}
    (hboundary : ∀ r : FaceSmoother p, r.faces = s.faces →
      μ.real {x | (∀ f ∈ r.faces, r.faceScore f x ≤ s.bandwidth * Real.log 2) ∧
        ¬(∀ f ∈ r.faces, r.faceScore f x ≤ -(s.bandwidth * Real.log 2))} ≤ M) :
    (∫ x, s.F x * (1 - s.F x) ∂μ) ≤ 2 * M := by
  let a := s.bandwidth * Real.log 2
  have ha : 0 ≤ a := mul_nonneg s.bandwidth_pos.le (Real.log_nonneg (by norm_num))
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
      (fun x => 2 * ((s.shiftOffsets a).F x - (s.shiftOffsets (-a)).F x)) μ :=
    (((hiF (s.shiftOffsets a)).sub (hiF (s.shiftOffsets (-a)))).const_mul 2)
  have hpoint := integral_mono_ae hiEnv hiDiff
    (Filter.Eventually.of_forall fun x => by
      simpa only [a, neg_mul] using s.smallerEnvelope_le_finite_difference x)
  have heq : (∫ x, 2 * ((s.shiftOffsets a).F x - (s.shiftOffsets (-a)).F x) ∂μ) =
      2 * ∫ e, (μ.real {x | ((s.shiftOffsets a).randomRectangle e).Inside x} -
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
  linarith


theorem upperFaceSmoother_face_scores_iff {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h)
    (s : FaceSmoother m) (hs : s.faces = (upperFaceSmoother a h hh).faces)
    (x : Vector r) (c : ℝ) :
    (∀ f ∈ s.faces, s.faceScore f (U.mulVec x) ≤ c) ↔
      ∀ j, faceDot (U j) x ≤ s.offsets (j, true)+c := by
  constructor
  · intro hx j
    have hf : (j, true) ∈ s.faces := by rw [hs]; simp [upperFaceSmoother]
    have hp := hx (j, true) hf
    change faceDot (U j) x-s.offsets (j, true) ≤ c at hp
    linarith
  · intro hx f hf
    rcases f with ⟨j, b⟩
    have hb : b = true := by
      rw [hs] at hf
      simpa only [upperFaceSmoother, Finset.mem_filter, Finset.mem_univ, true_and] using hf
    subst b
    change faceDot (U j) x-s.offsets (j, true) ≤ c
    linarith [hx j]

/-- Actual layer probabilities for all finite thresholds imply the
smaller-envelope expectation. Every law and integral is genuine. -/
theorem integral_logisticEnvelope_le_of_layer_bound
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Vector r) (hX : Measurable X)
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h M : ℝ} (hh : 0 < h)
    (hboundary : ∀ b : Vector m,
      μ.real {ω | X ω ∈ gaussianPolyhedronLayer U b (h*Real.log 2)} ≤ M) :
    (∫ ω, logisticNullWeight U a h (X ω)*(1-logisticNullWeight U a h (X ω)) ∂μ) ≤ 2*M := by
  let s := upperFaceSmoother a h hh
  let Z : Ω → Vector m := fun ω => U.mulVec (X ω)
  have hZ : Measurable Z := (measurable_rectangular_mulVec U).comp hX
  let ν := μ.map Z
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_map hZ.aemeasurable
  have hb : (∫ y, s.F y*(1-s.F y) ∂ν) ≤ 2*M := by
    apply integral_smallerEnvelope_le_of_matching_boundary s ν
    intro q hq
    have hm (c : ℝ) : MeasurableSet {y : Vector m | ∀ f ∈ q.faces, q.faceScore f y ≤ c} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
        measurableSet_le (q.continuous_faceScore f).measurable measurable_const))
    have hmS : MeasurableSet {y : Vector m |
        (∀ f ∈ q.faces, q.faceScore f y ≤ s.bandwidth*Real.log 2) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f y ≤ -(s.bandwidth*Real.log 2))} :=
      (hm _).inter (hm _).compl
    have hmap := map_measureReal_apply (μ := μ) hZ hmS
    rw [hmap]
    have hevent : {ω : Ω |
        (∀ f ∈ q.faces, q.faceScore f (Z ω) ≤ s.bandwidth*Real.log 2) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f (Z ω) ≤ -(s.bandwidth*Real.log 2))} =
        {ω : Ω | X ω ∈ gaussianPolyhedronLayer U (fun j => q.offsets (j, true)) (h*Real.log 2)} := by
      ext ω
      change ((∀ f ∈ q.faces, q.faceScore f (U.mulVec (X ω)) ≤ h*Real.log 2) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f (U.mulVec (X ω)) ≤ -(h*Real.log 2))) ↔ _
      rw [upperFaceSmoother_face_scores_iff U a hh q hq, upperFaceSmoother_face_scores_iff U a hh q hq]
      simp only [gaussianPolyhedronLayer, facePolyhedron, Set.mem_diff, Set.mem_setOf_eq,
        sub_eq_add_neg, faceDot, dotProduct]
    exact (congrArg (fun S => μ.real S) hevent).le.trans (hboundary _)
  have hf : Continuous (fun y : Vector m => s.F y*(1-s.F y)) :=
    s.continuous_F.mul (continuous_const.sub s.continuous_F)
  have hmap := integral_map (μ := μ) hZ.aemeasurable hf.aestronglyMeasurable
  rw [hmap] at hb
  simpa only [Z, s, Function.comp_apply, upperFaceSmoother_F] using hb

theorem continuous_logisticNullWeight {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h) :
    Continuous (logisticNullWeight U a h) := by
  have hc := (upperFaceSmoother a h hh).continuous_F.comp
    (show Continuous (fun x : Vector r => U.mulVec x) from continuous_const.matrix_mulVec continuous_id)
  change Continuous (fun x : Vector r => (upperFaceSmoother a h hh).F (U.mulVec x)) at hc
  simpa only [upperFaceSmoother_F] using hc

theorem logisticEnvelope_nonneg {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h) (x : Vector r) :
    0 ≤ logisticNullWeight U a h x*(1-logisticNullWeight U a h x) := by
  rw [← upperFaceSmoother_F U a h hh]
  exact mul_nonneg ((upperFaceSmoother a h hh).F_pos _).le
    (sub_nonneg.mpr ((upperFaceSmoother a h hh).F_le_one _))

theorem integrable_logisticEnvelope
    {Ω : Type*} [MeasurableSpace Ω] {m r : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Vector r) (hX : Measurable X)
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h) :
    Integrable (fun ω => logisticNullWeight U a h (X ω)*
      (1-logisticNullWeight U a h (X ω))) μ := by
  have hc := continuous_logisticNullWeight U a hh
  apply (integrable_const (1 : ℝ)).mono'
    ((hc.mul (continuous_const.sub hc)).measurable.comp hX).aestronglyMeasurable
  filter_upwards [] with ω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (logisticEnvelope_nonneg U a hh _)]
  have hF0 := ((upperFaceSmoother a h hh).F_pos (U.mulVec (X ω))).le
  have hF1 := (upperFaceSmoother a h hh).F_le_one (U.mulVec (X ω))
  rw [upperFaceSmoother_F] at hF0 hF1
  nlinarith [sq_nonneg (logisticNullWeight U a h (X ω))]

end
end RectangleCLT.Companion.SplitV4

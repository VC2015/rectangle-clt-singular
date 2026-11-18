import RectangleCLTArxivV1.SmoothingMatrixIntrinsic
import RectangleCLTCompanion.SelectorConcentration

/-! Uniform logistic transition and one-face reference masses from the
actual intrinsic layer concentration, before Gaussian averaging. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem intrinsicRectangleConcentration_transitionMassBound
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ h : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hh : 0 < h) (hδh : δ ≤ h)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ) :
    TransitionMassBound μ V h (4*C₀*h*κ) := by
  intro s hs z
  let τ := (μ.map V).map (fun x : Vector p => x+z)
  letI : IsProbabilityMeasure (μ.map V) := isProbabilityMeasure_map hV.aemeasurable
  letI : IsProbabilityMeasure τ := isProbabilityMeasure_map (measurable_id.add_const z).aemeasurable
  have hshift : Measurable (fun x : Vector p => x+z) := by fun_prop
  have hb (q : FaceSmoother p) :
      τ.real {x | (∀ f ∈ q.faces, q.faceScore f x ≤ s.bandwidth*Real.log 2) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f x ≤ -(s.bandwidth*Real.log 2))} ≤
        C₀*κ*(h*Real.log 2+δ) := by
    have hwidth : 0 < h*Real.log 2 := mul_pos hh (Real.log_pos (by norm_num))
    have he : {x | (∀ f ∈ q.faces, q.faceScore f x ≤ s.bandwidth*Real.log 2) ∧
        ¬(∀ f ∈ q.faces, q.faceScore f x ≤ -(s.bandwidth*Real.log 2))} =
        q.boundaryLayer (h*Real.log 2) := by
      ext x
      rw [q.mem_boundaryLayer_iff_score]
      simp only [Set.mem_setOf_eq,hs]
    rw [he]
    have hmap : τ.real (q.boundaryLayer (h*Real.log 2)) =
        (μ.map V).real {x | x+z ∈ q.boundaryLayer (h*Real.log 2)} :=
      map_measureReal_apply hshift (q.measurableSet_boundaryLayer _)
    rw [hmap]
    exact hc q z (h*Real.log 2) hwidth
  have hb' := s.integral_smallerEnvelope_le_of_boundary τ hb
  have hm : Measurable (fun x : Vector p => s.F x*(1-s.F x)) := by fun_prop
  have hmap : (∫ x, s.F x*(1-s.F x) ∂τ) =
      ∫ ω, s.F (V ω+z)*(1-s.F (V ω+z)) ∂μ := by
    calc
      _ = ∫ x, s.F (x+z)*(1-s.F (x+z)) ∂μ.map V :=
        integral_map hshift.aemeasurable hm.aestronglyMeasurable
      _ = _ := integral_map hV.aemeasurable ((hm.comp hshift).aestronglyMeasurable)

  rw [hmap] at hb'
  have hlog : Real.log (2:ℝ) ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at ht
    exact ht
  have hwidth : h*Real.log 2+δ ≤ 2*h := by nlinarith [mul_le_mul_of_nonneg_left hlog hh.le]
  have hbudget := mul_le_mul_of_nonneg_left hwidth (mul_nonneg hC₀ hκ)
  change (∫ ω, s.F (V ω+z)*(1-s.F (V ω+z)) ∂μ) ≤ _
  exact hb'.trans (by nlinarith only [hbudget])

/-- The intrinsic mass bound also covers every single-face reference. -/
theorem intrinsicRectangleConcentration_oneFaceMass
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ) (f : Face p) (z : Vector p) :
    (∫ ω, oneFaceReference s f (V ω+z) ∂μ) ≤ 4*C₀*s.bandwidth*κ :=
  (intrinsicRectangleConcentration_transitionMassBound μ V hV hC₀ hκ
    s.bandwidth_pos hδh hc).oneFace s rfl f z

/-- Every nonempty selector sum, with arbitrary later face labels,
retains the same intrinsic transition mass. -/
theorem intrinsicRectangleConcentration_selectorMass
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ) (K : ℕ) (z : Vector p) :
    (∫ ω, ∑ α : Fin (K+1) → Face p, selectorWeight s α (V ω+z) ∂μ) ≤
      4*C₀*s.bandwidth*κ :=
  (intrinsicRectangleConcentration_transitionMassBound μ V hV hC₀ hκ
    s.bandwidth_pos hδh hc).selectorSum hV s rfl K z

end
end RectangleCLTArxivV1

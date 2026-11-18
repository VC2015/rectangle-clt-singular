import RectangleCLTArxivV1.SupplementalHIntrinsicMass
import RectangleCLTArxivV1.SupplementalHCubicWeights

/-! Actual Gaussian-weighted selector masses obtained by conditioning on
the Gaussian vector and retaining the intrinsic transition coefficient. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem intrinsicRectangleConcentration_gaussianWeightedOneFaceMass
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (B : Vector r → ℝ) (hBm : Measurable B) (hB0 : ∀ g, 0 ≤ B g)
    (hBi : Integrable B (standardGaussian r)) (f : Face p) :
    (∫ ω, ∫ g, B g*oneFaceReference s f (V ω+M.mulVec g) ∂standardGaussian r ∂μ) ≤
      (4*C₀*s.bandwidth*κ)*(∫ g, B g ∂standardGaussian r) := by
  classical
  let W := fun z : Ω × Vector r => oneFaceReference s f (V z.1+M.mulVec z.2)
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hX : Measurable (fun z : Ω × Vector r => V z.1+M.mulVec z.2) :=
    (hV.comp measurable_fst).add (hM.comp measurable_snd)
  have hWm : Measurable W := by
    have hm : Measurable (oneFaceReference s f) := by
      unfold oneFaceReference FaceSmoother.faceScore FaceSmoother.normalDot
      cases hf : f.2 <;> simp [hf] <;> fun_prop
    exact hm.comp hX
  have hWb (z : Ω × Vector r) : 0 ≤ W z ∧ W z ≤ 1 := oneFaceReference_bounds s f _
  have hBprod : Integrable (fun z : Ω × Vector r => B z.2) (μ.prod (standardGaussian r)) := by
    apply (integrable_prod_iff ((hBm.comp measurable_snd).aestronglyMeasurable)).mpr
    refine ⟨ae_of_all _ (fun _ => hBi),?_⟩
    change Integrable (fun _ : Ω => ∫ g, ‖B g‖ ∂standardGaussian r) μ
    exact integrable_const _
  have hi : Integrable (fun z : Ω × Vector r => B z.2*W z) (μ.prod (standardGaussian r)) := by
    apply hBprod.mono' (((hBm.comp measurable_snd).mul hWm).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change |B z.2*W z| ≤ B z.2
      rw [abs_of_nonneg (mul_nonneg (hB0 z.2) (hWb z).1)]
      exact mul_le_of_le_one_right (hB0 z.2) (hWb z).2)
  have hpoint (g : Vector r) : (∫ ω, B g*W (ω,g) ∂μ) ≤ (4*C₀*s.bandwidth*κ)*B g := by
    rw [integral_const_mul]
    have ht := intrinsicRectangleConcentration_oneFaceMass μ V hV s hC₀ hκ hδh hc f (M.mulVec g)
    exact (mul_le_mul_of_nonneg_left ht (hB0 g)).trans_eq (mul_comm _ _)
  change (∫ ω, ∫ g, B g*W (ω,g) ∂standardGaussian r ∂μ) ≤ _
  rw [integral_integral_swap hi]
  exact (integral_mono hi.integral_prod_right (hBi.const_mul _) hpoint).trans_eq (integral_const_mul _ _)

/-- A positive linear factor has finite actual Gaussian mass, even though
it is unbounded. -/
theorem supplementalH_integrable_positiveDirection {r : ℕ} (u : Vector r) :
    Integrable (supplementalHPositiveDirection u) (standardGaussian r) := by
  have hm : Measurable (supplementalHPositiveDirection u) := by
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  apply (standardGaussian_integrable_faceDot u).abs.mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    rw [Real.norm_eq_abs,abs_of_nonneg (supplementalHPositiveDirection_nonneg u g)]
    exact max_le (le_abs_self _) (abs_nonneg _))

theorem supplementalH_integral_positiveDirection_le_one {r : ℕ} (u : Vector r)
    (hu : vectorNormSq u=1) :
    (∫ g, supplementalHPositiveDirection u g ∂standardGaussian r) ≤ 1 := by
  have hi := ((SignedSurface.standardGaussian_integrable_faceDot_sq u).add
    (integrable_const (1:ℝ))).div_const 2
  have hb (g : Vector r) : supplementalHPositiveDirection u g ≤ ((faceDot u g)^2+1)/2 := by
    have hx : supplementalHPositiveDirection u g ≤ |faceDot u g| := max_le (le_abs_self _) (abs_nonneg _)
    nlinarith [sq_nonneg (|faceDot u g|-1),sq_abs (faceDot u g)]
  have hh := integral_mono (supplementalH_integrable_positiveDirection u) hi hb
  rw [integral_div] at hh
  simp only [Pi.add_apply] at hh
  rw [integral_add (SignedSurface.standardGaussian_integrable_faceDot_sq u) (integrable_const (1:ℝ)),
    SignedSurface.standardGaussian_integral_faceDot_sq,hu] at hh
  simpa using hh

/-- Each signed one-face reference has averaged mass bounded by the same
intrinsic coefficient. No logarithm of the bandwidth or coefficient occurs. -/
theorem intrinsicRectangleConcentration_positiveOneFaceMass
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (u : Vector r) (hu : vectorNormSq u=1) (f : Face p) :
    (∫ ω, ∫ g, supplementalHPositiveDirection u g*
      oneFaceReference s f (V ω+M.mulVec g) ∂standardGaussian r ∂μ) ≤ 4*C₀*s.bandwidth*κ := by
  have hm : Measurable (supplementalHPositiveDirection u) := by
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  have hb := intrinsicRectangleConcentration_gaussianWeightedOneFaceMass μ V hV s M hC₀ hκ hδh hc
    (supplementalHPositiveDirection u) hm (supplementalHPositiveDirection_nonneg u)
    (supplementalH_integrable_positiveDirection u) f
  have hwidth := s.bandwidth_pos
  exact hb.trans (mul_le_of_le_one_right (by positivity)
    (supplementalH_integral_positiveDirection_le_one u hu))

end
end RectangleCLTArxivV1

import RectangleCLTArxivV1.SupplementalHPairProjectionLaw

/-! The native pair-reference estimate under the original projected
standard Gaussian law, without a nonsingularity hypothesis on the base. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem hReferencePair_projected_product_integral
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (u v : Vector r) (hu : vectorNormSq u=1) (hv : vectorNormSq v=1)
    (hρ : (faceDot u v)^2<1) (f g : Face p) (h σ a b : ℝ) :
    (∫ z, hReferencePair
      ((FaceSmoother.normalDot f (V z.1)+σ*faceDot u z.2-a)/h,
       (FaceSmoother.normalDot g (V z.1)+σ*faceDot v z.2-b)/h)
      ∂μ.prod (standardGaussian r)) =
    ∫ z, hReferencePair
      ((FaceSmoother.normalDot f (V z.1)+σ*z.2.1-a)/h,
       (FaceSmoother.normalDot g (V z.1)+σ*faceDot u v*z.2.1+
         σ*Real.sqrt (1-(faceDot u v)^2)*z.2.2-b)/h)
      ∂μ.prod ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let X := fun z : Ω × Vector r =>
    ((FaceSmoother.normalDot f (V z.1)+σ*faceDot u z.2-a)/h,
     (FaceSmoother.normalDot g (V z.1)+σ*faceDot v z.2-b)/h)
  let Y := fun z : Ω × (ℝ × ℝ) =>
    ((FaceSmoother.normalDot f (V z.1)+σ*z.2.1-a)/h,
     (FaceSmoother.normalDot g (V z.1)+σ*faceDot u v*z.2.1+
       σ*Real.sqrt (1-(faceDot u v)^2)*z.2.2-b)/h)
  have hfm := (FaceSmoother.continuous_normalDot f).measurable.comp hV
  have hgm := (FaceSmoother.continuous_normalDot g).measurable.comp hV
  have hX : Measurable X := by
    unfold X faceDot
    fun_prop
  have hY : Measurable Y := by
    unfold Y
    fun_prop
  have hiX := hReferencePair_integrable_probability (μ.prod (standardGaussian r)) X hX
  have hiY := hReferencePair_integrable_probability
    (μ.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))) Y hY
  change (∫ z, hReferencePair (X z) ∂μ.prod (standardGaussian r)) =
    ∫ z, hReferencePair (Y z) ∂μ.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))
  rw [integral_prod _ hiX,integral_prod _ hiY]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  let F := fun z : ℝ × ℝ => hReferencePair
    ((FaceSmoother.normalDot f (V ω)+σ*z.1-a)/h,
     (FaceSmoother.normalDot g (V ω)+σ*z.2-b)/h)
  have hF : Measurable F := measurable_hReferencePair.comp (by fun_prop)
  have he := hReferencePair_projected_integral u v hu hv hρ F hF
  calc
    _ = ∫ z, F (z.1,faceDot u v*z.1+Real.sqrt (1-(faceDot u v)^2)*z.2)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := he
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only [F,Y]
        congr 2
        ring)

/-- Pair reference mass for the original Gaussian projections. The
base may be singular, and only actual rectangle-layer concentration is used. -/
theorem intrinsicRectangleConcentration_pair_projected_reference_mass
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ h σ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hh : 0 < h) (hσ : 0 < σ) (hδh : δ ≤ h)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (u v : Vector r) (hu : vectorNormSq u=1) (hv : vectorNormSq v=1)
    (hρ : (faceDot u v)^2<1) (f g : Face p) (a b : ℝ) :
    (∫ z, hReferencePair
      ((FaceSmoother.normalDot f (V z.1)+σ*faceDot u z.2-a)/h,
       (FaceSmoother.normalDot g (V z.1)+σ*faceDot v z.2-b)/h)
      ∂μ.prod (standardGaussian r)) ≤
        2*C₀*h^2*κ/(σ*Real.sqrt (1-(faceDot u v)^2)) := by
  rw [hReferencePair_projected_product_integral μ V hV u v hu hv hρ f g h σ a b]
  exact intrinsicRectangleConcentration_pair_normal_reference_mass μ V hV hC₀ hκ
    hh hσ (Real.sqrt_pos.mpr (by linarith)) hδh hc (gaussianReal 0 1) f g
    (faceDot u v) a b

/-- The full angular weight cancels the correlation singularity before
any first-pair gap restriction is imposed. -/
theorem intrinsicRectangleConcentration_pair_projected_angular_reference_mass
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ h σ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hh : 0 < h) (hσ : 0 < σ) (hδh : δ ≤ h)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (u v : Vector r) (hu : vectorNormSq u=1) (hv : vectorNormSq v=1)
    (hρ : (faceDot u v)^2<1) (f g : Face p) (a b : ℝ) :
    (Real.arccos (faceDot u v)*Real.sqrt (1-(faceDot u v)^2)) *
      (∫ z, hReferencePair
        ((FaceSmoother.normalDot f (V z.1)+σ*faceDot u z.2-a)/h,
         (FaceSmoother.normalDot g (V z.1)+σ*faceDot v z.2-b)/h)
        ∂μ.prod (standardGaussian r)) ≤ 2*Real.pi*C₀*h^2*κ/σ := by
  rw [hReferencePair_projected_product_integral μ V hV u v hu hv hρ f g h σ a b]
  exact intrinsicRectangleConcentration_pair_angular_reference_mass μ V hV hC₀ hκ
    hh hσ (Real.sqrt_pos.mpr (by linarith)) hδh hc
    (mul_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right (Real.arccos_le_pi _) (Real.sqrt_nonneg _))
    (gaussianReal 0 1) f g (faceDot u v) a b

end
end RectangleCLTArxivV1

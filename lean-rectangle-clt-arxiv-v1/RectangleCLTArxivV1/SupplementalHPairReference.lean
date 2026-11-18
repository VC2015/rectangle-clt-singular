import RectangleCLTArxivV1.SupplementalHIntrinsicMass
import RectangleCLTArxivV1.CapLogisticMajorant
import RectangleCLTArxivV1.CapWeightMass
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/- Actual scalar profiles and Gaussian reference masses for Appendix H. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion
open scoped Topology NNReal ENNReal
noncomputable section

def hReferenceSingle (s : ℝ) : ℝ := Real.exp s / (1+Real.exp s)^2

def hReferencePair (z : ℝ × ℝ) : ℝ :=
  Real.exp z.1*Real.exp z.2/(1+Real.exp z.1+Real.exp z.2)^3

theorem measurable_hReferenceSingle : Measurable hReferenceSingle := by
  unfold hReferenceSingle
  fun_prop

theorem measurable_hReferencePair : Measurable hReferencePair := by
  unfold hReferencePair
  fun_prop

theorem hReferenceSingle_nonneg (s : ℝ) : 0 ≤ hReferenceSingle s := by
  unfold hReferenceSingle
  positivity

theorem hReferencePair_nonneg (z : ℝ × ℝ) : 0 ≤ hReferencePair z := by
  unfold hReferencePair
  positivity

theorem hReferenceSingle_le_capLaplace (s : ℝ) : hReferenceSingle s ≤ capLaplace s := by
  exact cap_logistic_single_le s (1+Real.exp s) (by linarith [Real.exp_nonneg s]) (by linarith)

theorem hReferencePair_le_capLaplace (z : ℝ × ℝ) :
    hReferencePair z ≤ capLaplace z.1*capLaplace z.2 := by
  exact cap_logistic_pair_le z.1 z.2 (1+Real.exp z.1+Real.exp z.2)
    (by linarith [Real.exp_nonneg z.1,Real.exp_nonneg z.2])
    (by linarith [Real.exp_nonneg z.2]) (by linarith [Real.exp_nonneg z.1])

theorem hReferenceSingle_le_one (s : ℝ) : hReferenceSingle s ≤ 1 :=
  (hReferenceSingle_le_capLaplace s).trans (capLaplace_le_one s)

theorem hReferencePair_le_one (z : ℝ × ℝ) : hReferencePair z ≤ 1 :=
  (hReferencePair_le_capLaplace z).trans (by
    have hh := mul_le_mul (capLaplace_le_one z.1) (capLaplace_le_one z.2)
      (capLaplace_nonneg z.2) zero_le_one
    simpa using hh)

theorem hReferenceSingle_integrable_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) : Integrable (fun ω => hReferenceSingle (X ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_hReferenceSingle.comp hX).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖hReferenceSingle (X ω)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (hReferenceSingle_nonneg _)]
    exact hReferenceSingle_le_one _)

theorem hReferencePair_integrable_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ × ℝ) (hX : Measurable X) : Integrable (fun ω => hReferencePair (X ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_hReferencePair.comp hX).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖hReferencePair (X ω)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (hReferencePair_nonneg _)]
    exact hReferencePair_le_one _)

theorem integrable_hReferenceSingle : Integrable hReferenceSingle volume := by
  apply integrable_capLaplace.mono' measurable_hReferenceSingle.aestronglyMeasurable
  exact ae_of_all _ (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hReferenceSingle_nonneg s)]
    exact hReferenceSingle_le_capLaplace s)

theorem integrable_hReferencePair : Integrable hReferencePair (volume.prod volume) := by
  apply (integrable_capLaplace.mul_prod integrable_capLaplace).mono'
    measurable_hReferencePair.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hReferencePair_nonneg z)]
    exact hReferencePair_le_capLaplace z)

theorem hReferenceSingle_integral : (∫ s, hReferenceSingle s) = 1 := by
  have hd (s : ℝ) : HasDerivAt (fun t => -(1+Real.exp t)⁻¹) (hReferenceSingle s) s := by
    convert ((((hasDerivAt_const s (1 : ℝ)).add (Real.hasDerivAt_exp s)).inv
      (by positivity)).neg) using 1 <;> simp only [hReferenceSingle,neg_div,neg_neg,zero_add]
  have hb : Tendsto (fun s : ℝ => -(1+Real.exp s)⁻¹) atBot (𝓝 (-1 : ℝ)) := by
    simpa using ((tendsto_const_nhds.add Real.tendsto_exp_atBot).inv₀ (by norm_num : (1 : ℝ)+0≠0)).neg
  have ht : Tendsto (fun s : ℝ => -(1+Real.exp s)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun s : ℝ => 1+Real.exp s) atTop atTop :=
      tendsto_const_nhds.add_atTop Real.tendsto_exp_atTop
    simpa using (tendsto_inv_atTop_zero.comp hh).neg
  simpa using integral_of_hasDerivAt_of_tendsto hd integrable_hReferenceSingle hb ht

theorem hReferencePair_inner_integral (s : ℝ) :
    (∫ t, hReferencePair (s,t)) = (1/2 : ℝ)*hReferenceSingle s := by
  let a := 1+Real.exp s
  have ha : 0 < a := by dsimp [a]; positivity
  have hi : Integrable (fun t => hReferencePair (s,t)) volume := by
    apply (integrable_capLaplace.const_mul (capLaplace s)).mono'
      (measurable_hReferencePair.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact ae_of_all _ (fun t => by
      change ‖hReferencePair (s,t)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (hReferencePair_nonneg (s,t))]
      exact hReferencePair_le_capLaplace (s,t))
  have hd (t : ℝ) : HasDerivAt (fun x => (-Real.exp s/2)*((a+Real.exp x)⁻¹)^2)
      (hReferencePair (s,t)) t := by
    convert (((((hasDerivAt_const t a).add (Real.hasDerivAt_exp t)).inv (by positivity)).pow 2).const_mul
      (-Real.exp s/2)) using 1
    dsimp [hReferencePair,a]
    field_simp
    ring
  have hb : Tendsto (fun t : ℝ => (-Real.exp s/2)*((a+Real.exp t)⁻¹)^2) atBot
      (𝓝 ((-Real.exp s/2)*(a⁻¹)^2)) := by
    simpa using (((tendsto_const_nhds.add Real.tendsto_exp_atBot).inv₀
      (by simpa using ha.ne' : a+0≠0)).pow 2).const_mul (-Real.exp s/2)
  have ht : Tendsto (fun t : ℝ => (-Real.exp s/2)*((a+Real.exp t)⁻¹)^2) atTop (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun t : ℝ => a+Real.exp t) atTop atTop :=
      tendsto_const_nhds.add_atTop Real.tendsto_exp_atTop
    simpa using ((tendsto_inv_atTop_zero.comp hh).pow 2).const_mul (-Real.exp s/2)
  have hh := integral_of_hasDerivAt_of_tendsto hd hi hb ht
  convert hh using 1
  dsimp [hReferenceSingle,a]
  field_simp

/-- The exact two-score reference integral displayed in the pair proof. -/
theorem hReferencePair_integral : (∫ z, hReferencePair z ∂volume.prod volume) = 1/2 := by
  rw [integral_prod _ integrable_hReferencePair]
  simp_rw [hReferencePair_inner_integral]
  rw [integral_const_mul,hReferenceSingle_integral]
  ring

/-- A quantitative lower envelope for the one-score reference. -/
theorem hReferenceSingle_lower (s : ℝ) :
    Real.exp (-|s|)/4 ≤ hReferenceSingle s := by
  have he := Real.exp_pos s
  have hd : 0 < Real.exp (-s)+2+Real.exp s := by positivity
  have hid : hReferenceSingle s = 1/(Real.exp (-s)+2+Real.exp s) := by
    unfold hReferenceSingle
    rw [Real.exp_neg]
    field_simp
    ring
  have hE : 1 ≤ Real.exp |s| := Real.one_le_exp (abs_nonneg s)
  have hp : Real.exp s ≤ Real.exp |s| := Real.exp_le_exp.mpr (le_abs_self s)
  have hn : Real.exp (-s) ≤ Real.exp |s| := Real.exp_le_exp.mpr (neg_le_abs s)
  have hi : Real.exp (-|s|)/4 = 1/(4*Real.exp |s|) := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hid,hi]
  apply (div_le_div_iff₀ (by positivity) hd).mpr
  nlinarith

/-- A Gaussian density is bounded by a fixed multiple of the logistic
reference; intrinsic one-face concentration therefore controls convolution. -/
theorem hReference_gaussianPDF_le (s : ℝ) :
    gaussianPDFReal 0 1 s ≤ 4*Real.exp (1/2 : ℝ)*hReferenceSingle s := by
  have hsqrt : 1 ≤ Real.sqrt (2*Real.pi) :=
    Real.one_le_sqrt.mpr (by linarith [Real.two_le_pi])
  have hi : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt
  have hφ : gaussianPDFReal 0 1 s ≤ Real.exp (-s^2/2) := by
    change (Real.sqrt (2*Real.pi*1))⁻¹*Real.exp (-(s-0)^2/(2*1)) ≤ _
    simpa using mul_le_mul_of_nonneg_right hi (Real.exp_nonneg (-s^2/2))
  have hq : -s^2/2 ≤ (1/2 : ℝ)-|s| := by
    nlinarith [sq_nonneg (|s|-1),sq_abs s]
  calc
    _ ≤ Real.exp (-s^2/2) := hφ
    _ ≤ Real.exp ((1/2 : ℝ)-|s|) := Real.exp_le_exp.mpr hq
    _ = (4*Real.exp (1/2 : ℝ))*(Real.exp (-|s|)/4) := by
      rw [Real.exp_sub,Real.exp_neg]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hReferenceSingle_lower s) (by positivity)

theorem hReference_gaussianPDF_le_one (s : ℝ) : gaussianPDFReal 0 1 s ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt (2*Real.pi) :=
    Real.one_le_sqrt.mpr (by linarith [Real.two_le_pi])
  have hi : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt
  have he : Real.exp (-s^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg s])
  change (Real.sqrt (2*Real.pi*1))⁻¹*Real.exp (-(s-0)^2/(2*1)) ≤ _
  simpa using mul_le_one₀ hi (by positivity) he

/-- Uniform density bound for an actual coordinate marginal after Gaussian
convolution, including singular laws of the unsmoothed vector. -/
theorem intrinsicRectangleConcentration_gaussian_marginal_density
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ σ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hσ : 0 < σ) (hδσ : δ ≤ σ)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ) (f : Face p) (a : ℝ) :
    (∫ ω, gaussianPDFReal 0 1 ((FaceSmoother.normalDot f (V ω)-a)/σ)/σ ∂μ) ≤
      16*Real.exp (1/2 : ℝ)*C₀*κ := by
  classical
  let s : FaceSmoother p := ⟨{f},fun _ => a,σ,hσ⟩
  let X := fun ω => (FaceSmoother.normalDot f (V ω)-a)/σ
  have hX : Measurable X :=
    (((FaceSmoother.continuous_normalDot f).measurable.comp hV).sub_const a).div_const σ
  have href : (∫ ω, hReferenceSingle (X ω) ∂μ) ≤ 4*C₀*σ*κ := by
    simpa [oneFaceReference,hReferenceSingle,FaceSmoother.faceScore,s,X] using
      intrinsicRectangleConcentration_oneFaceMass μ V hV s hC₀ hκ hδσ hc f 0
  have hpi : Integrable (fun ω => gaussianPDFReal 0 1 (X ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_gaussianPDFReal 0 1).comp hX).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      change ‖gaussianPDFReal 0 1 (X ω)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      exact hReference_gaussianPDF_le_one _)
  have hri : Integrable (fun ω => hReferenceSingle (X ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_hReferenceSingle.comp hX).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      change ‖hReferenceSingle (X ω)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (hReferenceSingle_nonneg _)]
      simpa [oneFaceReference,hReferenceSingle,FaceSmoother.faceScore,s,X] using
        (oneFaceReference_bounds s f (V ω)).2)
  have hm := integral_mono hpi (hri.const_mul (4*Real.exp (1/2 : ℝ)))
    (fun ω => hReference_gaussianPDF_le (X ω))
  rw [integral_const_mul] at hm
  have hb := hm.trans (mul_le_mul_of_nonneg_left href (by positivity : 0 ≤ 4*Real.exp (1/2 : ℝ)))
  change (∫ ω, gaussianPDFReal 0 1 (X ω)/σ ∂μ) ≤ _
  rw [integral_div]
  apply (div_le_iff₀ hσ).mpr
  convert hb using 1 <;> ring

/-- The genuine conditional density in coordinates
`(V₁+σG₁,V₂+σρG₁+σνG₂)`. -/
def hReferenceConditionalPairDensity (σ ν ρ v₁ v₂ x y : ℝ) : ℝ :=
  (gaussianPDFReal 0 1 ((v₁-x)/σ)/σ)*
    (gaussianPDFReal 0 1 ((v₂+ρ*(x-v₁)-y)/(σ*ν))/(σ*ν))

theorem hReferenceConditionalPairDensity_nonneg {σ ν : ℝ}
    (hσ : 0 ≤ σ) (hν : 0 ≤ ν) (ρ v₁ v₂ x y : ℝ) :
    0 ≤ hReferenceConditionalPairDensity σ ν ρ v₁ v₂ x y := by
  unfold hReferenceConditionalPairDensity
  exact mul_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) hσ)
    (div_nonneg (gaussianPDFReal_nonneg _ _ _) (mul_nonneg hσ hν))

theorem intrinsicRectangleConcentration_gaussian_pair_density
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ σ ν : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hσ : 0 < σ) (hν : 0 < ν) (hδσ : δ ≤ σ)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (f g : Face p) (ρ x y : ℝ) :
    (∫ ω, hReferenceConditionalPairDensity σ ν ρ
      (FaceSmoother.normalDot f (V ω)) (FaceSmoother.normalDot g (V ω)) x y ∂μ) ≤
      16*Real.exp (1/2 : ℝ)*C₀*κ/(σ*ν) := by
  let X := fun ω => (FaceSmoother.normalDot f (V ω)-x)/σ
  let Y := fun ω => (FaceSmoother.normalDot g (V ω)+ρ*(x-FaceSmoother.normalDot f (V ω))-y)/(σ*ν)
  have hX : Measurable X := by
    exact (((FaceSmoother.continuous_normalDot f).measurable.comp hV).sub_const x).div_const σ
  have hY : Measurable Y := by
    dsimp only [Y]
    exact ((((FaceSmoother.continuous_normalDot g).measurable.comp hV).add
      (((measurable_const.sub ((FaceSmoother.continuous_normalDot f).measurable.comp hV))).const_mul ρ)).sub_const y).div_const _
  have hm : Measurable (fun ω => (gaussianPDFReal 0 1 (X ω)/σ)*
      (gaussianPDFReal 0 1 (Y ω)/(σ*ν))) :=
    (((measurable_gaussianPDFReal 0 1).comp hX).div_const _).mul
      (((measurable_gaussianPDFReal 0 1).comp hY).div_const _)
  have hfirst (ω : Ω) : 0 ≤ gaussianPDFReal 0 1 (X ω)/σ :=
    div_nonneg (gaussianPDFReal_nonneg _ _ _) hσ.le
  have hsecond (ω : Ω) : gaussianPDFReal 0 1 (Y ω)/(σ*ν) ≤ 1/(σ*ν) :=
    div_le_div_of_nonneg_right (hReference_gaussianPDF_le_one _) (mul_pos hσ hν).le
  have hpi : Integrable (fun ω => gaussianPDFReal 0 1 (X ω)/σ) μ := by
    apply (integrable_const (1/σ)).mono'
      (((measurable_gaussianPDFReal 0 1).comp hX).div_const _).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      change ‖gaussianPDFReal 0 1 (X ω)/σ‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (hfirst ω)]
      exact div_le_div_of_nonneg_right (hReference_gaussianPDF_le_one _) hσ.le)
  have hbound (ω : Ω) : (gaussianPDFReal 0 1 (X ω)/σ)*
      (gaussianPDFReal 0 1 (Y ω)/(σ*ν)) ≤
      (1/(σ*ν))*(gaussianPDFReal 0 1 (X ω)/σ) := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hsecond ω) (hfirst ω)
  have hprod : Integrable (fun ω => (gaussianPDFReal 0 1 (X ω)/σ)*
      (gaussianPDFReal 0 1 (Y ω)/(σ*ν))) μ := by
    apply (hpi.const_mul (1/(σ*ν))).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hfirst ω)
        (div_nonneg (gaussianPDFReal_nonneg _ _ _) (mul_pos hσ hν).le))]
      exact hbound ω)
  have hb := integral_mono hprod (hpi.const_mul (1/(σ*ν))) hbound
  rw [integral_const_mul] at hb
  have hmain := intrinsicRectangleConcentration_gaussian_marginal_density μ V hV
    hC₀ hκ hσ hδσ hc f x
  change (∫ ω, (gaussianPDFReal 0 1 (X ω)/σ)*
    (gaussianPDFReal 0 1 (Y ω)/(σ*ν)) ∂μ) ≤ _
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 1/(σ*ν))
    simpa [X,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh)

theorem hReference_normal_integral_le_volume (F : ℝ → ℝ) (hFm : Measurable F)
    (hFi : Integrable F volume) (hF0 : ∀ t, 0 ≤ F t) :
    (∫ t, F t ∂gaussianReal 0 1) ≤ ∫ t, F t := by
  have he : (∫ t, F t ∂gaussianReal 0 1) =
      ∫ t, gaussianPDFReal 0 1 t*F t := by
    rw [gaussianReal_of_var_ne_zero 0 (by simp : (1 : ℝ≥0) ≠ 0),gaussianPDF_def,
      integral_withDensity_eq_integral_toReal_smul
        (measurable_gaussianPDFReal 0 1).ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul]
  have hb (t : ℝ) : gaussianPDFReal 0 1 t*F t ≤ F t := by
    simpa using mul_le_mul_of_nonneg_right (hReference_gaussianPDF_le_one t) (hF0 t)
  have hi : Integrable (fun t => gaussianPDFReal 0 1 t*F t) volume := by
    apply hFi.mono' ((measurable_gaussianPDFReal 0 1).mul hFm).aestronglyMeasurable
    exact ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hF0 t))]
      exact hb t)
  rw [he]
  exact integral_mono hi hFi hb

theorem hReferencePair_normal_fiber_bound (s c : ℝ) {h σ ν : ℝ}
    (hh : 0 < h) (hσ : 0 < σ) (hν : 0 < ν) :
    (∫ t, hReferencePair (s,(c+σ*ν*t)/h) ∂gaussianReal 0 1) ≤
      h/(2*σ*ν)*hReferenceSingle s := by
  let q := σ*ν/h
  have hq : 0 < q := div_pos (mul_pos hσ hν) hh
  have hf : Integrable (fun t => hReferencePair (s,t)) volume := by
    apply (integrable_capLaplace.const_mul (capLaplace s)).mono'
      (measurable_hReferencePair.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact ae_of_all _ (fun t => by
      change ‖hReferencePair (s,t)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (hReferencePair_nonneg _)]
      exact hReferencePair_le_capLaplace _)
  have he (t : ℝ) : (c+σ*ν*t)/h = q*t+c/h := by dsimp [q]; ring
  have hi : Integrable (fun t => hReferencePair (s,(c+σ*ν*t)/h)) volume := by
    simp_rw [he]
    exact (hf.comp_add_right (c/h)).comp_mul_left' hq.ne'
  calc
    _ ≤ ∫ t, hReferencePair (s,(c+σ*ν*t)/h) := by
      apply hReference_normal_integral_le_volume _ _ hi (fun _ => hReferencePair_nonneg _)
      unfold hReferencePair
      fun_prop
    _ = h/(2*σ*ν)*hReferenceSingle s := by
      simp_rw [he]
      rw [Measure.integral_comp_mul_left (fun t => hReferencePair (s,t+c/h)) q]
      rw [integral_add_right_eq_self (fun t => hReferencePair (s,t)) (c/h),
        hReferencePair_inner_integral,abs_of_pos (inv_pos.mpr hq),smul_eq_mul]
      dsimp [q]
      field_simp [hh.ne',hσ.ne',hν.ne'] <;> ring <;> simp

theorem intrinsicRectangleConcentration_oneFace_normal_average
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ h : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hh : 0 < h) (hδh : δ ≤ h)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (η : Measure ℝ) [IsProbabilityMeasure η] (f : Face p) (σ a : ℝ) :
    (∫ ω, ∫ t, hReferenceSingle ((FaceSmoother.normalDot f (V ω)+σ*t-a)/h) ∂η ∂μ) ≤
      4*C₀*h*κ := by
  classical
  have hm : Measurable (fun z : Ω × ℝ => (FaceSmoother.normalDot f (V z.1)+σ*z.2-a)/h) :=
    (((((FaceSmoother.continuous_normalDot f).measurable.comp hV).comp measurable_fst).add
      (measurable_snd.const_mul σ)).sub_const a).div_const h
  have hi := hReferenceSingle_integrable_probability (μ.prod η) _ hm
  rw [integral_integral_swap hi]
  have hb (t : ℝ) : (∫ ω, hReferenceSingle ((FaceSmoother.normalDot f (V ω)+σ*t-a)/h) ∂μ) ≤
      4*C₀*h*κ := by
    let s : FaceSmoother p := ⟨{f},fun _ => a-σ*t,h,hh⟩
    have he (ω : Ω) : FaceSmoother.normalDot f (V ω)+σ*t-a =
        FaceSmoother.normalDot f (V ω)-(a-σ*t) := by ring
    simp_rw [he]
    simpa [oneFaceReference,hReferenceSingle,FaceSmoother.faceScore,s] using
      intrinsicRectangleConcentration_oneFaceMass μ V hV s hC₀ hκ hδh hc f 0
  calc
    _ ≤ ∫ _ : ℝ, 4*C₀*h*κ ∂η := by
      apply integral_mono_of_nonneg
        (ae_of_all _ (fun t => integral_nonneg (fun ω => hReferenceSingle_nonneg _)))
        (integrable_const _)
      exact ae_of_all _ hb
    _ = _ := by simp

/-- The actual pair reference mass. The first Gaussian coordinate can
have any probability law; the orthogonal coordinate is standard normal. -/
theorem intrinsicRectangleConcentration_pair_normal_reference_mass
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ h σ ν : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hh : 0 < h) (hσ : 0 < σ) (hν : 0 < ν) (hδh : δ ≤ h)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (η : Measure ℝ) [IsProbabilityMeasure η] (f g : Face p) (ρ a b : ℝ) :
    (∫ z, hReferencePair
      ((FaceSmoother.normalDot f (V z.1)+σ*z.2.1-a)/h,
       (FaceSmoother.normalDot g (V z.1)+σ*ρ*z.2.1+σ*ν*z.2.2-b)/h)
      ∂μ.prod (η.prod (gaussianReal 0 1))) ≤ 2*C₀*h^2*κ/(σ*ν) := by
  let S := fun ω t => (FaceSmoother.normalDot f (V ω)+σ*t-a)/h
  let T := fun ω t u => (FaceSmoother.normalDot g (V ω)+σ*ρ*t+σ*ν*u-b)/h
  let c := h/(2*σ*ν)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hm : Measurable (fun z : Ω × (ℝ × ℝ) => (S z.1 z.2.1,T z.1 z.2.1 z.2.2)) := by
    unfold S T
    apply Measurable.prodMk
    · exact (((((FaceSmoother.continuous_normalDot f).measurable.comp hV).comp measurable_fst).add
        ((measurable_fst.comp measurable_snd).const_mul σ)).sub_const a).div_const h
    · exact ((((((FaceSmoother.continuous_normalDot g).measurable.comp hV).comp measurable_fst).add
        ((measurable_fst.comp measurable_snd).const_mul (σ*ρ))).add
        ((measurable_snd.comp measurable_snd).const_mul (σ*ν))).sub_const b).div_const h
  have hi := hReferencePair_integrable_probability (μ.prod (η.prod (gaussianReal 0 1))) _ hm
  have hSm : Measurable (fun z : Ω × ℝ => S z.1 z.2) := by
    unfold S
    exact (((((FaceSmoother.continuous_normalDot f).measurable.comp hV).comp measurable_fst).add
      (measurable_snd.const_mul σ)).sub_const a).div_const h
  have hSi := hReferenceSingle_integrable_probability (μ.prod η) _ hSm
  have hb (ω : Ω) (t : ℝ) :
      (∫ u, hReferencePair (S ω t,T ω t u) ∂gaussianReal 0 1) ≤ c*hReferenceSingle (S ω t) := by
    have he (u : ℝ) : T ω t u = (FaceSmoother.normalDot g (V ω)+σ*ρ*t-b+σ*ν*u)/h := by
      dsimp [T]
      ring
    simp_rw [he]
    exact hReferencePair_normal_fiber_bound (S ω t)
      (FaceSmoother.normalDot g (V ω)+σ*ρ*t-b) hh hσ hν
  change (∫ z, hReferencePair (S z.1 z.2.1,T z.1 z.2.1 z.2.2)
    ∂μ.prod (η.prod (gaussianReal 0 1))) ≤ _
  calc
    _ = ∫ ω, ∫ t, ∫ u, hReferencePair (S ω t,T ω t u) ∂gaussianReal 0 1 ∂η ∂μ := by
      rw [integral_prod _ hi]
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => integral_prod _
        (hReferencePair_integrable_probability (η.prod (gaussianReal 0 1)) _
          (by simpa using hm.comp (measurable_const.prodMk measurable_id))))
    _ ≤ ∫ ω, c*(∫ t, hReferenceSingle (S ω t) ∂η) ∂μ := by
      apply integral_mono_of_nonneg
        (ae_of_all _ (fun ω => integral_nonneg (fun t => integral_nonneg
          (fun u => hReferencePair_nonneg _))))
        (hSi.integral_prod_left.const_mul c)
      exact ae_of_all _ (fun ω => by
        change (∫ t, ∫ u, hReferencePair (S ω t,T ω t u) ∂gaussianReal 0 1 ∂η) ≤
          c*(∫ t, hReferenceSingle (S ω t) ∂η)
        rw [← integral_const_mul]
        apply integral_mono_of_nonneg
          (ae_of_all _ (fun t => integral_nonneg (fun u => hReferencePair_nonneg _)))
          ((hReferenceSingle_integrable_probability η _
            (by simpa using hSm.comp (measurable_const.prodMk measurable_id))).const_mul c)
        exact ae_of_all _ (hb ω))
    _ = c*(∫ ω, ∫ t, hReferenceSingle (S ω t) ∂η ∂μ) := integral_const_mul _ _
    _ ≤ c*(4*C₀*h*κ) := mul_le_mul_of_nonneg_left
      (intrinsicRectangleConcentration_oneFace_normal_average μ V hV hC₀ hκ hh hδh hc η f σ a) hc0
    _ = _ := by dsimp [c]; ring

theorem intrinsicRectangleConcentration_pair_angular_reference_mass
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    {C₀ δ κ h σ ν ℓ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (hh : 0 < h) (hσ : 0 < σ) (hν : 0 < ν) (hδh : δ ≤ h)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hl0 : 0 ≤ ℓ) (hl : ℓ ≤ Real.pi*ν)
    (η : Measure ℝ) [IsProbabilityMeasure η] (f g : Face p) (ρ a b : ℝ) :
    ℓ*(∫ z, hReferencePair
      ((FaceSmoother.normalDot f (V z.1)+σ*z.2.1-a)/h,
       (FaceSmoother.normalDot g (V z.1)+σ*ρ*z.2.1+σ*ν*z.2.2-b)/h)
      ∂μ.prod (η.prod (gaussianReal 0 1))) ≤ 2*Real.pi*C₀*h^2*κ/σ := by
  have hb := intrinsicRectangleConcentration_pair_normal_reference_mass
    μ V hV hC₀ hκ hh hσ hν hδh hc η f g ρ a b
  have hR : 0 ≤ 2*C₀*h^2*κ/(σ*ν) := by positivity
  calc
    _ ≤ ℓ*(2*C₀*h^2*κ/(σ*ν)) := mul_le_mul_of_nonneg_left hb hl0
    _ ≤ (Real.pi*ν)*(2*C₀*h^2*κ/(σ*ν)) := mul_le_mul_of_nonneg_right hl hR
    _ = _ := by field_simp; ring

end
end RectangleCLTArxivV1

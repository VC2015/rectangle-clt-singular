import RectangleCLTArxivV1.SupplementalHFourthTransportFacetSum
import RectangleCLTArxivV1.SupplementalHFourthTransportRegularity

/-! Actual localized J_f surface estimate after an arbitrary independent
base. Affine exceptional thresholds are removed by genuine product Fubini. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem measurable_thresholdSignedSection_threshold {m r : ℕ}
    (u : Fin m → Vector r) (j : Fin m) :
    Measurable (fun b => Printed.thresholdSignedSection u b j (b j)) := by
  let E : Set (Vector m × Vector r) := {z | ∀ l∈Finset.univ.erase j,
    faceDot (gaussianNormalProjection (u j) (u l)) z.2≤z.1 l-z.1 j*faceDot (u l) (u j)}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro l
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((continuous_faceDot_left _).measurable.comp measurable_snd)
      (((measurable_pi_apply l).comp measurable_fst).sub (((measurable_pi_apply j).comp measurable_fst).mul_const _))
  let S := fun z : Vector m × Vector r => vectorNormSq (gaussianSectionPoint (u j) (z.1 j) z.2)-(r:ℝ)
  have hS : Measurable S := by
    unfold S gaussianSectionPoint gaussianSectionResidual vectorNormSq faceDot
    fun_prop
  have hi := (hS.indicator hE).stronglyMeasurable.integral_prod_right' (ν := standardGaussian r)
  exact hi.measurable

theorem measurable_hardGaussianWeightedFacetIntegral {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1) :
    Measurable (hardGaussianWeightedFacetIntegral u) := by
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have he : hardGaussianWeightedFacetIntegral u=fun b =>
      ∑ j, |b j| *(gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u b j (b j)) := by
    funext b
    unfold hardGaussianWeightedFacetIntegral
    apply Finset.sum_congr rfl
    intro j _
    rw [hardGaussianFacetIntegral_eq_signedSection u b j (hu j)]
  rw [he]
  exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).abs.mul
    ((hpdf.measurable.comp (measurable_pi_apply j)).mul (measurable_thresholdSignedSection_threshold u j)))

theorem fourthTransport_measurableSet_gaussianOutwardVariableTube {r m : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (σ : ℝ)
    (R : Vector r → ℝ) (hR : Measurable R) :
    MeasurableSet (gaussianOutwardVariableTube U a σ R) := by
  have hX : Measurable (fun z : Vector r × Vector r => z.1+σ • z.2) :=
    measurable_fst.add (measurable_const.smul measurable_snd)
  have hproj (j : Fin m) : Measurable (fun z : Vector r × Vector r => faceDot (U j) (z.1+σ • z.2)) :=
    (continuous_faceDot_left (U j)).measurable.comp hX
  have hr : Measurable (fun z : Vector r × Vector r => σ/R z.2) := measurable_const.div (hR.comp measurable_snd)
  change MeasurableSet ({z : Vector r × Vector r | ∀ j,faceDot (U j) (z.1+σ • z.2)≤a j+σ/R z.2} \
    {z | ∀ j,faceDot (U j) (z.1+σ • z.2)≤a j+0})
  simp only [setOf_forall]
  exact (MeasurableSet.iInter (fun j => measurableSet_le (hproj j) (measurable_const.add hr))).diff
    (MeasurableSet.iInter (fun j => measurableSet_le (hproj j) measurable_const))

/-- Actual surface quantity averaged against an arbitrary base probability
law. Its integrability follows from the true common Gaussian R4 moment. -/
theorem hardGaussianWeightedFacetIntegral_base_tube_bound {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {σ : ℝ} (hσ : 0<σ) (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ᵐ x ∂ν,∀ j,ResidualThresholdRegularity (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) j) :
    Integrable (fun x => hardGaussianWeightedFacetIntegral (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
    (∫ x,|hardGaussianWeightedFacetIntegral (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ z,(gaussianOutwardVariableTube (fun k => U (f k)) a σ
        (supplementalHRadius U)).indicator (fun z => supplementalHRadius U z.2^4) z ∂ν.prod (standardGaussian (n+1))) := by
  let C := 16384*Real.exp ((3:ℝ)/2)
  let J := fun x => hardGaussianWeightedFacetIntegral (fun k => U (f k))
    (fun k => (a k-faceDot (U (f k)) x)/σ)
  let I := (gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U)).indicator
    (fun z => supplementalHRadius U z.2^4)
  have hIset := fourthTransport_measurableSet_gaussianOutwardVariableTube (fun k => U (f k)) a σ
    (supplementalHRadius U) (measurable_supplementalHRadius U)
  have hi : Integrable I (ν.prod (standardGaussian (n+1))) := by
    have hr : Integrable (fun z : Vector (n+1) × Vector (n+1) => supplementalHRadius U z.2^4)
        (ν.prod (standardGaussian (n+1))) := by
      simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod (supplementalHRadius_moment_le hp U 4).1
    exact hr.indicator hIset
  have hJ : Measurable J := (measurable_hardGaussianWeightedFacetIntegral (fun k => U (f k)) hu).comp
    (by apply measurable_pi_lambda; intro k; exact (measurable_const.sub (measurable_thresholdDot _)).div_const σ)
  have hb : ∀ᵐ x ∂ν,|J x|≤C*(∫ g,I (x,g) ∂standardGaussian (n+1)) := by
    filter_upwards [hreg] with x hx
    exact (abs_hardGaussianWeightedFacetIntegral_le_coefficient_sum _ _ hu hx).trans
      (fourthGreenTubeCoefficient_affine_sum_le hp U f a x hσ hu hx)
  have hJi : Integrable J ν := (hi.integral_prod_left.const_mul C).mono' hJ.aestronglyMeasurable
    (hb.mono (fun _ h => by simpa only [Real.norm_eq_abs] using h))
  refine ⟨hJi,?_⟩
  have hh := integral_mono_ae hJi.abs (hi.integral_prod_left.const_mul C) hb
  rw [integral_const_mul,← integral_prod _ hi] at hh
  exact hh

/-- The actual J_f estimate for volume-almost every threshold list. The
base law may be singular. Its only probability premise is the displayed
concentration hypothesis for that base. -/
theorem ae_hardGaussianWeightedFacetIntegral_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun k => U (f k)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => hardGaussianWeightedFacetIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
      (∫ x,|hardGaussianWeightedFacetIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)≤
        (16384*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  filter_upwards [ae_threshold_ae_base_residualThresholdRegularity ν (fun k => U (f k)) hσ.ne'] with a ha
  have hh := hardGaussianWeightedFacetIntegral_base_tube_bound hp ν U f a hσ hu ha
  refine ⟨hh.1,hh.2.trans ?_⟩
  have ht := concentrated_base_threeFace_weighted_outward_tube hp ν (fun k => U (f k)) a U hK hδ hσ hbase
  exact (mul_le_mul_of_nonneg_left ht (by positivity : 0≤16384*Real.exp ((3:ℝ)/2))).trans_eq (by ring)

end
end RectangleCLTArxivV1

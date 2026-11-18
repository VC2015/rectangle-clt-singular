import RectangleCLTCompanion.SplitV4.GaussianThresholdSections

/-! Actual affine Euclidean surface measure from the archived orthogonal
normal chart. Raw mathlib Hausdorff measure is diameter-normalized; the
chart volume here uses the usual Euclidean Lebesgue normalization. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SignedSurface
open RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section

theorem measurable_normalSectionChart {n : ℕ} (j : Fin (n+1)) (u : Vector (n+1)) (b : ℝ) :
    Measurable (normalSectionChart j u b) := by
  have hi : Measurable (fun y : Vector n => (j.insertNth b y : Vector (n+1))) := by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k=j
    · subst k
      simp
    · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hk
      simpa using (measurable_pi_apply l : Measurable (fun y : Vector n => y l))
  exact (gaussianRotation (coordinateNormalRotation j u)).measurable.comp hi

/-- The ambient Gaussian density factorizes exactly in the existing
orthogonal tangent chart; no coarea or surface estimate is assumed. -/
theorem gaussianDensity_normalSectionChart {n : ℕ} (j : Fin (n+1))
    (u : Vector (n+1)) (b : ℝ) (y : Vector n) :
    standardGaussianDensity (n+1) (normalSectionChart j u b y)=
      gaussianPDFReal 0 1 b*standardGaussianDensity n y := by
  rw [standardGaussianDensity_eq_kernel,standardGaussianDensity_eq_kernel]
  unfold RectangleCLT.gaussianKernel
  rw [vectorNormSq_normalSectionChart]
  rw [pow_succ]
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [show -(b^2+vectorNormSq y)/2 = -(b^2)/2+(-vectorNormSq y/2) by ring,Real.exp_add]
  ring

/-- Canonically normalized Euclidean affine volume, constructed from an
actual orthogonal chart. Independence of the chart is proved below. -/
def affineSurfaceVolume {n : ℕ} (j : Fin (n+1)) (u : Vector (n+1)) (b : ℝ) :
    Measure (Vector (n+1)) := (volume : Measure (Vector n)).map (normalSectionChart j u b)

theorem gaussianSection_integral_eq_normalSectionChart {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ)
    (f : Vector (n+1) → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ x, |f x|≤C) :
    (∫ z, f (gaussianSectionPoint u b z) ∂standardGaussian (n+1))=
      ∫ y, f (normalSectionChart j u b y) ∂standardGaussian n := by
  have hi : Integrable (fun z => f (gaussianSectionPoint u b z)) (standardGaussian (n+1)) :=
    (integrable_const C).mono'
      (hf.comp (measurable_gaussianSectionPoint u b)).aestronglyMeasurable
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hbound _))
  rw [standardGaussian_integral_normal_sections j u hi]
  simp only [gaussianSectionPoint_normalSectionChart j u hu,integral_const,
    measureReal_univ_eq_one,one_smul]

/-- The concrete affine Gaussian law is exactly the Gaussian tangent
coordinate law pushed along the actual chart. -/
theorem gaussianSectionLaw_eq_chart_map {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ) :
    gaussianSectionLaw u b=(standardGaussian n).map (normalSectionChart j u b) := by
  have hmap : Measurable (normalSectionChart j u b) := measurable_normalSectionChart j u b
  haveI : IsProbabilityMeasure ((standardGaussian n).map (normalSectionChart j u b)) :=
    isProbabilityMeasure_map hmap.aemeasurable
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (gaussianSectionLaw u b).real s=((standardGaussian n).map (normalSectionChart j u b)).real s
  rw [←integral_indicator_one hs,←integral_indicator_one hs]
  unfold gaussianSectionLaw
  change (∫ x, s.indicator (fun _ => (1:ℝ)) x ∂(standardGaussian (n+1)).map (gaussianSectionPoint u b))=
    ∫ x, s.indicator (fun _ => (1:ℝ)) x ∂(standardGaussian n).map (normalSectionChart j u b)
  rw [integral_map (measurable_gaussianSectionPoint u b).aemeasurable
      (measurable_const.indicator hs).aestronglyMeasurable,
    integral_map hmap.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable]
  exact gaussianSection_integral_eq_normalSectionChart j u hu b (s.indicator (fun _ => 1))
    (measurable_const.indicator hs) 1 (fun x => by by_cases hx : x ∈ s <;> simp [hx])

/-- Density weighting commutes with a measurable pushforward when the
weight is a function of the actual image point. -/
theorem map_weighted_density {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f) (ρ : Y → ℝ≥0∞) (hρ : Measurable ρ) :
    (μ.map f).withDensity ρ=(μ.withDensity (fun x => ρ (f x))).map f := by
  apply Measure.ext
  intro s hs
  rw [withDensity_apply _ hs,Measure.map_apply hf hs,withDensity_apply _ (hf hs)]
  rw [←lintegral_indicator hs,lintegral_map (hρ.indicator hs) hf,
    ←lintegral_indicator (hf hs)]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ s <;> simp [hx]

/-- Exact Gaussian weighting of the actual affine surface measure. This
measure identity holds for all hard measurable face restrictions. -/
theorem affineSurfaceVolume_gaussian_weight {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ) :
    (affineSurfaceVolume j u b).withDensity
      (fun x => ENNReal.ofReal (standardGaussianDensity (n+1) x))=
      ENNReal.ofReal (gaussianPDFReal 0 1 b) • gaussianSectionLaw u b := by
  rw [affineSurfaceVolume,map_weighted_density _ _ (measurable_normalSectionChart j u b) _
    (standardGaussianDensity_measurable (n+1)).ennreal_ofReal]
  have he : (fun y : Vector n => ENNReal.ofReal
      (standardGaussianDensity (n+1) (normalSectionChart j u b y)))=
      ENNReal.ofReal (gaussianPDFReal 0 1 b) •
        (fun y => ENNReal.ofReal (standardGaussianDensity n y)) := by
    funext y
    rw [gaussianDensity_normalSectionChart,ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    rfl
  rw [he,withDensity_smul _ (standardGaussianDensity_measurable n).ennreal_ofReal,
    ←standardGaussian_eq_withDensity,Measure.map_smul,←gaussianSectionLaw_eq_chart_map j u hu b]

/-- The affine Euclidean volume is independent of the chosen coordinate
normal chart. Positivity of the actual Gaussian density cancels the weight. -/
theorem affineSurfaceVolume_chart_independent {n : ℕ}
    (j k : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ) :
    affineSurfaceVolume j u b=affineSurfaceVolume k u b := by
  let ρ := fun x : Vector (n+1) => ENNReal.ofReal (standardGaussianDensity (n+1) x)
  have hρ : Measurable ρ := (standardGaussianDensity_measurable (n+1)).ennreal_ofReal
  have hp (μ : Measure (Vector (n+1))) : ∀ᵐ x ∂μ, ρ x≠0 :=
    ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos _ _)).ne')
  have ht (μ : Measure (Vector (n+1))) : ∀ᵐ x ∂μ, ρ x≠∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_ne_top)
  have he : (affineSurfaceVolume j u b).withDensity ρ=(affineSurfaceVolume k u b).withDensity ρ :=
    (affineSurfaceVolume_gaussian_weight j u hu b).trans
      (affineSurfaceVolume_gaussian_weight k u hu b).symm
  have hh := congrArg (fun μ : Measure (Vector (n+1)) => μ.withDensity (fun x => (ρ x)⁻¹)) he
  simpa only [withDensity_inv_same hρ (hp _) (ht _)] using hh


/-- The constructed surface volume lives on the actual supporting
hyperplane, rather than on an abstract surrogate set. -/
theorem affineSurfaceVolume_ae_on_hyperplane {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ) :
    ∀ᵐ x ∂affineSurfaceVolume j u b, faceDot u x=b := by
  unfold affineSurfaceVolume
  apply (ae_map_iff (measurable_normalSectionChart j u b).aemeasurable
    ((continuous_faceDot_left u).measurable (measurableSet_singleton b))).mpr
  exact ae_of_all _ (fun y => normalSectionChart_on_hyperplane j u hu b y)

/-- Exact Gaussian surface integration for every genuine measurable hard
face test, with the scalar normal density retained. -/
theorem affineSurfaceVolume_gaussian_integral {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ)
    (f : Vector (n+1) → ℝ) :
    (∫ x, standardGaussianDensity (n+1) x*f x ∂affineSurfaceVolume j u b)=
      gaussianPDFReal 0 1 b*(∫ x, f x ∂gaussianSectionLaw u b) := by
  have hh := integral_withDensity_eq_integral_toReal_smul
    (μ := affineSurfaceVolume j u b) (f := fun x => ENNReal.ofReal (standardGaussianDensity (n+1) x))
    (standardGaussianDensity_measurable (n+1)).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (g := f)
  rw [affineSurfaceVolume_gaussian_weight j u hu b,integral_smul_measure] at hh
  simpa only [ENNReal.toReal_ofReal (standardGaussianDensity_pos _ _).le,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul] using hh.symm

/-- The actual signed score is integrable under the concrete affine
Gaussian section law, including after any hard measurable restriction. -/
theorem gaussianSectionLaw_integrable_score_indicator {r : ℕ}
    (u : Vector r) (hu : vectorNormSq u=1) (b : ℝ) (P : Set (Vector r)) (hP : MeasurableSet P) :
    Integrable (P.indicator (fun x => vectorNormSq x-(r:ℝ))) (gaussianSectionLaw u b) := by
  have hm : Measurable (fun x : Vector r => vectorNormSq x-(r:ℝ)) := by
    unfold vectorNormSq
    fun_prop
  apply Integrable.indicator _ hP
  unfold gaussianSectionLaw
  apply (integrable_map_measure hm.aestronglyMeasurable
    (measurable_gaussianSectionPoint u b).aemeasurable).mpr
  exact (standardGaussian_integrable_sectionPoint_normSq u b hu).sub (integrable_const _)

/-- A genuine hard polyhedral face has exactly the conditional-Gaussian
surface formula. There is no assumed bound on a surface functional. -/
theorem hardFacet_signed_surface_eq_section {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ)
    (P : Set (Vector (n+1))) (hP : MeasurableSet P) :
    (∫ x in P, (vectorNormSq x-((n+1:ℕ):ℝ))*standardGaussianDensity (n+1) x
      ∂affineSurfaceVolume j u b)=
      gaussianPDFReal 0 1 b*(∫ x in P, vectorNormSq x-((n+1:ℕ):ℝ) ∂gaussianSectionLaw u b) := by
  rw [←integral_indicator hP,←integral_indicator hP]
  have hh := affineSurfaceVolume_gaussian_integral j u hu b
    (P.indicator (fun x => vectorNormSq x-((n+1:ℕ):ℝ)))
  convert hh using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by by_cases hx : x ∈ P <;> simp [hx,mul_comm])


/-- Gaussian-weighted affine surface integrability is equivalent to
ordinary integrability under the actual section probability law. -/
theorem affineSurfaceVolume_gaussian_integrable_iff {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ)
    (f : Vector (n+1) → ℝ) :
    Integrable (fun x => standardGaussianDensity (n+1) x*f x) (affineSurfaceVolume j u b) ↔
      Integrable f (gaussianSectionLaw u b) := by
  have hh := integrable_withDensity_iff_integrable_smul'
    (μ := affineSurfaceVolume j u b)
    (standardGaussianDensity_measurable (n+1)).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (g := f)
  rw [affineSurfaceVolume_gaussian_weight j u hu b,
    integrable_smul_measure (ENNReal.ofReal_pos.mpr (gaussianPDFReal_pos 0 1 b one_ne_zero)).ne'
      ENNReal.ofReal_ne_top] at hh
  simpa only [ENNReal.toReal_ofReal (standardGaussianDensity_pos _ _).le,smul_eq_mul] using hh.symm

/-- In particular, the hard-facet signed surface integral above is a
finite genuine expectation, not a totalized nonintegrable integral. -/
theorem hardFacet_signed_surface_integrable {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (hu : vectorNormSq u=1) (b : ℝ)
    (P : Set (Vector (n+1))) (hP : MeasurableSet P) :
    Integrable (P.indicator (fun x => (vectorNormSq x-((n+1:ℕ):ℝ))*standardGaussianDensity (n+1) x))
      (affineSurfaceVolume j u b) := by
  have hh := (affineSurfaceVolume_gaussian_integrable_iff j u hu b
    (P.indicator (fun x => vectorNormSq x-((n+1:ℕ):ℝ)))).mpr
      (gaussianSectionLaw_integrable_score_indicator u hu b P hP)
  convert hh using 1
  funext x
  by_cases hx : x ∈ P <;> simp [hx,mul_comm]

end
end RectangleCLTArxivV1

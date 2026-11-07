import RectangleCLTCompanion.SplitV4.GaussianThresholdSections
import RectangleCLT.GaussianStein

/-! Genuine derivatives of the hard Gaussian threshold probability.
The normal-section probabilities are actual Gaussian measures, and their
continuity is proved by null hyperplanes and dominated convergence. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem gaussianThresholdSectionProbability_nonneg {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (v : Vector r) (t : ℝ) :
    0 ≤ gaussianThresholdSectionProbability s u b v t := measureReal_nonneg

theorem gaussianThresholdSectionProbability_le_one {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (v : Vector r) (t : ℝ) :
    gaussianThresholdSectionProbability s u b v t ≤ 1 := measureReal_le_one

/-- Exact one-dimensional Gaussian disintegration for an individual
threshold coordinate. All other hard inequalities are retained. -/
theorem gaussianThresholdCDF_update_eq_section_integral {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (c : ℝ) :
    gaussianThresholdCDF u (Function.update b j c) =
      ∫ t in Iic c, gaussianPDFReal 0 1 t *
        gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) t := by
  classical
  let E := gaussianFiniteThresholdEvent Finset.univ u (Function.update b j c)
  have hE : MeasurableSet E := measurableSet_gaussianFiniteThresholdEvent _ _ _
  let f := E.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hE
  have hb (z) : |f z| ≤ 1 := by by_cases hz : z ∈ E <;> simp [f, hz]
  have hdis := standardGaussian_integral_section_product (0 : Fin (n + 1)) (u j) hu f hf 1 hb
  have hleft : gaussianThresholdCDF u (Function.update b j c) =
      ∫ z, f z ∂standardGaussian (n + 1) := by
    simpa only [gaussianThresholdCDF, E, gaussianFiniteThresholdEvent, Finset.mem_univ,
      forall_true_left, f] using (integral_indicator_one hE).symm
  rw [hleft, hdis]
  have hinner (t : ℝ) : (∫ z, f (SignedSurface.gaussianSectionPoint (u j) t z)
      ∂standardGaussian (n + 1)) =
      (Iic c).indicator
        (gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j)) t := by
    have hsec := SignedSurface.measurable_gaussianSectionPoint (u j) t
    have hi : (∫ z, f (SignedSurface.gaussianSectionPoint (u j) t z) ∂standardGaussian (n + 1)) =
        (standardGaussian (n + 1)).real ((SignedSurface.gaussianSectionPoint (u j) t) ⁻¹' E) := by
      exact integral_indicator_one (hE.preimage hsec)
    rw [hi]
    by_cases htc : t ≤ c
    · simp only [Set.indicator, Set.mem_Iic, if_pos htc]
      rw [gaussianThresholdSectionProbability_eq_section]
      congr 1
      ext z
      simp only [Set.mem_preimage, E, gaussianFiniteThresholdEvent, Set.mem_setOf_eq,
        Finset.mem_univ, forall_true_left, Finset.mem_erase, ne_eq, true_and, and_true]
      constructor
      · intro h l hlj
        simpa only [Function.update_of_ne hlj] using h l
      · intro h l
        by_cases hlj : l = j
        · subst l
          simpa only [Function.update_self, SignedSurface.gaussianSectionPoint_on_hyperplane (u j) t hu] using htc
        · simpa only [Function.update_of_ne hlj] using h l hlj
    · simp only [Set.indicator, Set.mem_Iic, if_neg htc]
      have he : (SignedSurface.gaussianSectionPoint (u j) t) ⁻¹' E = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro z hz
        have hj := hz j (Finset.mem_univ j)
        rw [Function.update_self, SignedSurface.gaussianSectionPoint_on_hyperplane (u j) t hu] at hj
        exact htc hj
      rw [he, measureReal_empty]
  rw [integral_congr_ae (ae_of_all _ hinner)]
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    by_cases htc : t ∈ Iic c <;> simp [htc, smul_eq_mul]

theorem hasDerivAt_integral_Iic_of_continuous_integrable (f : ℝ → ℝ)
    (hc : Continuous f) (hi : Integrable f volume) (x : ℝ) :
    HasDerivAt (fun y => ∫ t in Iic y, f t) (f x) x := by
  have he (y : ℝ) : (∫ t in Iic y, f t) = (∫ t in (0 : ℝ)..y, f t) + ∫ t in Iic 0, f t :=
    sub_eq_iff_eq_add.mp (intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const (∫ t in Iic 0, f t)
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall he)

/-- The genuine first coordinate derivative is the actual normal-section
probability multiplied by the one-dimensional Gaussian density. -/
theorem hasDerivAt_gaussianThresholdCDF_update {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1)
    (hp : ∀ l ∈ Finset.univ.erase j, gaussianNormalProjection (u j) (u l) ≠ 0) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdCDF u (Function.update b j t))
      (gaussianPDFReal 0 1 c * gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) c) c := by
  have hc := continuous_gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) hp
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hprob : Integrable (gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)]
      exact gaussianThresholdSectionProbability_le_one _ _ _ _ _)
  have hi := standardRealGaussian_integrable_density_mul hprob
  have hd := hasDerivAt_integral_Iic_of_continuous_integrable _ (hpdf.mul hc) hi c
  have he : (fun t => gaussianThresholdCDF u (Function.update b j t)) =
      fun t => ∫ s in Iic t, gaussianPDFReal 0 1 s *
        gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) s :=
    funext (gaussianThresholdCDF_update_eq_section_integral u b j hu)
  rw [he]
  exact hd

theorem gaussianThresholdFirst_eq_section {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdFirst u b j = gaussianPDFReal 0 1 (b j) *
      gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) (b j) := by
  exact (hasDerivAt_gaussianThresholdCDF_update u b j hu
    (fun l hl => gaussianNormalProjection_ne_zero_of_independent u hi j l (Finset.mem_erase.mp hl).1) (b j)).deriv

theorem continuous_gaussianThresholdFirst {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (fun b => gaussianThresholdFirst u b j) := by
  have hp := continuous_gaussianFiniteThresholdCDF (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l hl => gaussianNormalProjection_ne_zero_of_independent u hi j l (Finset.mem_erase.mp hl).1)
  have hb : Continuous (fun b : Vector m => fun l => b l - b j * faceDot (u l) (u j)) :=
    continuous_pi (fun l => (continuous_apply l).sub ((continuous_apply j).mul continuous_const))
  have hpdf : Continuous (fun b : Vector m => gaussianPDFReal 0 1 (b j)) :=
    (continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)).comp
      (continuous_apply j)
  have hc := hpdf.mul (hp.comp hb)
  have he : (fun b => gaussianThresholdFirst u b j) = fun b => gaussianPDFReal 0 1 (b j) *
      gaussianFiniteThresholdCDF (Finset.univ.erase j) (fun l => gaussianNormalProjection (u j) (u l))
        (fun l => b l - b j * faceDot (u l) (u j)) :=
    funext (fun b => gaussianThresholdFirst_eq_section u b j hu hi)
  rw [he]
  exact hc

theorem hasDerivAt_gaussianThresholdCDF_update_first {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdCDF u (Function.update b j t))
      (gaussianThresholdFirst u (Function.update b j c) j) c := by
  have hd := hasDerivAt_gaussianThresholdCDF_update u b j hu
    (fun l hl => gaussianNormalProjection_ne_zero_of_independent u hi j l (Finset.mem_erase.mp hl).1) c
  have he : gaussianThresholdFirst u (Function.update b j c) j =
      gaussianPDFReal 0 1 c * gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) c := by
    unfold gaussianThresholdFirst
    simp only [Function.update_self, Function.update_idem]
    exact hd.deriv
  rw [he]
  exact hd

end
end RectangleCLT.Companion.SplitV4

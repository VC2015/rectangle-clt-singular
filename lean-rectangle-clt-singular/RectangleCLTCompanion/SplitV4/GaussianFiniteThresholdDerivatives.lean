import RectangleCLTCompanion.SplitV4.GaussianThresholdDerivatives

/-! The exact coordinate-section derivative for a retained finite face set.
This allows conditioning once more without inserting zero dummy normals. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem gaussianFiniteThresholdCDF_update_eq_section_integral {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m) (hj : j ∈ s)
    (hu : vectorNormSq (u j) = 1) (c : ℝ) :
    gaussianFiniteThresholdCDF s u (Function.update b j c) =
      ∫ t in Iic c, gaussianPDFReal 0 1 t *
        gaussianThresholdSectionProbability (s.erase j) u b (u j) t := by
  classical
  let E := gaussianFiniteThresholdEvent s u (Function.update b j c)
  have hE : MeasurableSet E := measurableSet_gaussianFiniteThresholdEvent _ _ _
  let f := E.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hE
  have hb (z) : |f z| ≤ 1 := by by_cases hz : z ∈ E <;> simp [f, hz]
  have hdis := standardGaussian_integral_section_product (0 : Fin (n + 1)) (u j) hu f hf 1 hb
  have hleft : gaussianFiniteThresholdCDF s u (Function.update b j c) =
      ∫ z, f z ∂standardGaussian (n + 1) :=
    (integral_indicator_one hE).symm
  rw [hleft, hdis]
  have hinner (t : ℝ) : (∫ z, f (SignedSurface.gaussianSectionPoint (u j) t z)
      ∂standardGaussian (n + 1)) =
      (Iic c).indicator (gaussianThresholdSectionProbability (s.erase j) u b (u j)) t := by
    have hsec := SignedSurface.measurable_gaussianSectionPoint (u j) t
    have hi : (∫ z, f (SignedSurface.gaussianSectionPoint (u j) t z) ∂standardGaussian (n + 1)) =
        (standardGaussian (n + 1)).real ((SignedSurface.gaussianSectionPoint (u j) t) ⁻¹' E) :=
      integral_indicator_one (hE.preimage hsec)
    rw [hi]
    by_cases htc : t ≤ c
    · simp only [Set.indicator, Set.mem_Iic, if_pos htc]
      rw [gaussianThresholdSectionProbability_eq_section]
      congr 1
      ext z
      change (∀ l ∈ s, faceDot (u l) (SignedSurface.gaussianSectionPoint (u j) t z) ≤ Function.update b j c l) ↔
        ∀ l ∈ s.erase j, faceDot (u l) (SignedSurface.gaussianSectionPoint (u j) t z) ≤ b l
      constructor
      · intro h l hl
        obtain ⟨hlj, hls⟩ := Finset.mem_erase.mp hl
        simpa only [Function.update_of_ne hlj] using h l hls
      · intro h l hl
        by_cases hlj : l = j
        · subst l
          simpa only [Function.update_self, SignedSurface.gaussianSectionPoint_on_hyperplane (u j) t hu] using htc
        · simpa only [Function.update_of_ne hlj] using h l (Finset.mem_erase.mpr ⟨hlj, hl⟩)
    · simp only [Set.indicator, Set.mem_Iic, if_neg htc]
      have he : (SignedSurface.gaussianSectionPoint (u j) t) ⁻¹' E = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro z hz
        have hj' := hz j hj
        rw [Function.update_self, SignedSurface.gaussianSectionPoint_on_hyperplane (u j) t hu] at hj'
        exact htc hj'
      rw [he, measureReal_empty]
  rw [integral_congr_ae (ae_of_all _ hinner)]
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by by_cases htc : t ∈ Iic c <;> simp [htc, smul_eq_mul]

theorem hasDerivAt_gaussianFiniteThresholdCDF_update_unit {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m) (hj : j ∈ s)
    (hu : vectorNormSq (u j) = 1)
    (hp : ∀ l ∈ s.erase j, gaussianNormalProjection (u j) (u l) ≠ 0) (c : ℝ) :
    HasDerivAt (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))
      (gaussianPDFReal 0 1 c * gaussianThresholdSectionProbability (s.erase j) u b (u j) c) c := by
  have hc := continuous_gaussianThresholdSectionProbability (s.erase j) u b (u j) hp
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hprob : Integrable (gaussianThresholdSectionProbability (s.erase j) u b (u j)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)]
      exact gaussianThresholdSectionProbability_le_one _ _ _ _ _)
  have hi := standardRealGaussian_integrable_density_mul hprob
  have hd := hasDerivAt_integral_Iic_of_continuous_integrable _ (hpdf.mul hc) hi c
  have he : (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t)) =
      fun t => ∫ z in Iic t, gaussianPDFReal 0 1 z *
        gaussianThresholdSectionProbability (s.erase j) u b (u j) z :=
    funext (gaussianFiniteThresholdCDF_update_eq_section_integral s u b j hj hu)
  rw [he]
  exact hd

theorem gaussianFiniteThresholdCDF_rescale_one_normal {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    gaussianFiniteThresholdCDF s u (Function.update b j c) =
      gaussianFiniteThresholdCDF s (Function.update u j (σ⁻¹ • u j)) (Function.update b j (c / σ)) := by
  classical
  unfold gaussianFiniteThresholdCDF gaussianFiniteThresholdEvent
  congr 1
  ext g
  simp only [mem_setOf_eq]
  apply forall_congr'
  intro l
  apply forall_congr'
  intro _hl
  by_cases hlj : l = j
  · subst l
    simp only [Function.update_self, threshold_faceDot_smul_left]
    simpa only [div_eq_mul_inv, mul_comm] using (div_le_div_iff_of_pos_right hσ (a := faceDot (u j) g) (b := c)).symm
  · simp only [Function.update_of_ne hlj]

theorem gaussianThresholdSectionProbability_update_ignored {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (q v : Vector r) (t : ℝ) :
    gaussianThresholdSectionProbability (s.erase j) (Function.update u j v) b q t =
      gaussianThresholdSectionProbability (s.erase j) u b q t := by
  classical
  rw [gaussianThresholdSectionProbability_eq_section, gaussianThresholdSectionProbability_eq_section]
  congr 1
  ext z
  simp only [mem_setOf_eq]
  constructor <;> intro h l hl <;>
    simpa only [Function.update_of_ne (Finset.mem_erase.mp hl).1] using h l hl

theorem gaussianThresholdSectionProbability_update_levels_ignored {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (q : Vector r) (t c : ℝ) :
    gaussianThresholdSectionProbability (s.erase j) u (Function.update b j c) q t =
      gaussianThresholdSectionProbability (s.erase j) u b q t := by
  classical
  rw [gaussianThresholdSectionProbability_eq_section, gaussianThresholdSectionProbability_eq_section]
  congr 1
  ext z
  simp only [mem_setOf_eq]
  constructor <;> intro h l hl <;>
    simpa only [Function.update_of_ne (Finset.mem_erase.mp hl).1] using h l hl

/-- A nonunit selected normal is normalized explicitly, retaining the
Jacobian `1/sigma`; this is needed for genuine mixed section densities. -/
theorem hasDerivAt_gaussianFiniteThresholdCDF_update {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m) (hj : j ∈ s)
    {σ : ℝ} (hσ : 0 < σ) (hnorm : vectorNormSq (u j) = σ ^ 2)
    (hp : ∀ l ∈ s.erase j, gaussianNormalProjection (σ⁻¹ • u j) (u l) ≠ 0) (c : ℝ) :
    HasDerivAt (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))
      ((gaussianPDFReal 0 1 (c / σ) / σ) *
        gaussianThresholdSectionProbability (s.erase j) u b (σ⁻¹ • u j) (c / σ)) c := by
  classical
  let v := Function.update u j (σ⁻¹ • u j)
  have hunit : vectorNormSq (v j) = 1 := by
    simp only [v, Function.update_self, vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow,
      ← Finset.mul_sum]
    change σ⁻¹ ^ 2 * vectorNormSq (u j) = 1
    rw [hnorm]
    field_simp
  have hproj (l : Fin m) (hl : l ∈ s.erase j) : gaussianNormalProjection (v j) (v l) ≠ 0 := by
    simpa only [v, Function.update_self, Function.update_of_ne (Finset.mem_erase.mp hl).1] using hp l hl
  have hd := hasDerivAt_gaussianFiniteThresholdCDF_update_unit s v b j hj hunit hproj (c / σ)
  have hd' := hd.comp c ((hasDerivAt_id c).div_const σ)
  have he : (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t)) =
      fun t => gaussianFiniteThresholdCDF s v (Function.update b j (t / σ)) :=
    funext (gaussianFiniteThresholdCDF_rescale_one_normal s u b j hσ)
  rw [he]
  convert hd' using 1
  rw [gaussianThresholdSectionProbability_update_ignored]
  simp only [v, Function.update_self]
  ring

def gaussianFiniteThresholdFirst {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : ℝ :=
  deriv (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t)) (b j)

theorem gaussianFiniteThresholdCDF_update_outside {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (hj : j ∉ s) (c : ℝ) :
    gaussianFiniteThresholdCDF s u (Function.update b j c) = gaussianFiniteThresholdCDF s u b := by
  classical
  unfold gaussianFiniteThresholdCDF gaussianFiniteThresholdEvent
  congr 1
  ext g
  simp only [mem_setOf_eq]
  constructor <;> intro h l hl <;>
    simpa only [Function.update_of_ne (show l ≠ j from fun he => hj (he ▸ hl))] using h l hl

theorem gaussianFiniteThresholdFirst_outside {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (hj : j ∉ s) :
    gaussianFiniteThresholdFirst s u b j = 0 := by
  unfold gaussianFiniteThresholdFirst
  have he : (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t)) =
      fun _ => gaussianFiniteThresholdCDF s u b := funext (gaussianFiniteThresholdCDF_update_outside s u b j hj)
  rw [he, deriv_const]

theorem gaussianFiniteThresholdFirst_eq_section {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m) (hj : j ∈ s)
    {σ : ℝ} (hσ : 0 < σ) (hnorm : vectorNormSq (u j) = σ ^ 2)
    (hp : ∀ l ∈ s.erase j, gaussianNormalProjection (σ⁻¹ • u j) (u l) ≠ 0) :
    gaussianFiniteThresholdFirst s u b j = (gaussianPDFReal 0 1 (b j / σ) / σ) *
      gaussianThresholdSectionProbability (s.erase j) u b (σ⁻¹ • u j) (b j / σ) :=
  (hasDerivAt_gaussianFiniteThresholdCDF_update s u b j hj hσ hnorm hp (b j)).deriv

theorem continuous_gaussianFiniteThresholdFirst {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n + 1)) (j : Fin m) (hj : j ∈ s)
    {σ : ℝ} (hσ : 0 < σ) (hnorm : vectorNormSq (u j) = σ ^ 2)
    (hp : ∀ l ∈ s.erase j, gaussianNormalProjection (σ⁻¹ • u j) (u l) ≠ 0) :
    Continuous (fun b => gaussianFiniteThresholdFirst s u b j) := by
  have hc := continuous_gaussianFiniteThresholdCDF (s.erase j)
    (fun l => gaussianNormalProjection (σ⁻¹ • u j) (u l)) hp
  have hlev : Continuous (fun b : Vector m => fun l => b l - (b j / σ) * faceDot (u l) (σ⁻¹ • u j)) := by
    fun_prop
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hcoeff : Continuous (fun b : Vector m => gaussianPDFReal 0 1 (b j / σ) / σ) := by
    fun_prop
  have ht := hcoeff.mul (hc.comp hlev)
  have he : (fun b => gaussianFiniteThresholdFirst s u b j) = fun b =>
      (gaussianPDFReal 0 1 (b j / σ) / σ) *
        gaussianFiniteThresholdCDF (s.erase j) (fun l => gaussianNormalProjection (σ⁻¹ • u j) (u l))
          (fun l => b l - (b j / σ) * faceDot (u l) (σ⁻¹ • u j)) :=
    funext (fun b => gaussianFiniteThresholdFirst_eq_section s u b j hj hσ hnorm hp)
  rw [he]
  exact ht

theorem hasDerivAt_gaussianFiniteThresholdCDF_update_first {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m) (hj : j ∈ s)
    {σ : ℝ} (hσ : 0 < σ) (hnorm : vectorNormSq (u j) = σ ^ 2)
    (hp : ∀ l ∈ s.erase j, gaussianNormalProjection (σ⁻¹ • u j) (u l) ≠ 0) (c : ℝ) :
    HasDerivAt (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))
      (gaussianFiniteThresholdFirst s u (Function.update b j c) j) c := by
  have hd := hasDerivAt_gaussianFiniteThresholdCDF_update s u b j hj hσ hnorm hp c
  have he : gaussianFiniteThresholdFirst s u (Function.update b j c) j =
      (gaussianPDFReal 0 1 (c / σ) / σ) *
        gaussianThresholdSectionProbability (s.erase j) u b (σ⁻¹ • u j) (c / σ) := by
    unfold gaussianFiniteThresholdFirst
    simp only [Function.update_self, Function.update_idem]
    exact hd.deriv
  rw [he]
  exact hd

end
end RectangleCLT.Companion.SplitV4

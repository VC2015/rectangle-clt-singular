import RectangleCLTCompanion.SignedSurfaceTubeDomains
import RectangleCLT.GaussianTubeTransport

/-! Actual transport of arbitrary measurable tube domains into the common
Gaussian/exponential experiment. The output density cancels exactly. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def ratioWeightOf {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (g : Vector p → ℝ) (ze : Vector p × (ℝ × (Face p → ℝ))) : ℝ :=
  (imageEventOf S s A r B D).indicator (fun ze =>
    (standardGaussianDensity p (base (imagePreimage S s A (r, ze))) /
      standardGaussianDensity p ze.1) *
        g (base (imagePreimage S s A (r, ze)))) ze

theorem ratioWeightOf_measurable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (g : Vector p → ℝ) (hg : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    Measurable (ratioWeightOf S s A r B D g) := by
  have hp : Measurable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      imagePreimage S s A (r, ze)) :=
    (measurable_imagePreimage S s A).comp (measurable_const.prodMk measurable_id)
  have hb : Measurable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      base (imagePreimage S s A (r, ze))) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp hp)
  have hevent : MeasurableSet (imageEventOf S s A r B D) :=
    (measurableSet_imageEventOf_joint S s A hB hD hd).preimage
      (measurable_const.prodMk measurable_id)
  exact ((((standardGaussianDensity_measurable p).comp hb).div
    ((standardGaussianDensity_measurable p).comp measurable_fst)).mul
      (hg.comp hb)).indicator hevent

theorem measurableSet_image_sourceDomainOf {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {E₀ : ℝ} (hE₀ : 0 < E₀) (e : Face p → ℝ)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    MeasurableSet (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
      sourceDomainOf S s A r E₀ e B D) :=
  measurableSet_map_image (normalMatrix S A) s.bandwidth_pos.ne' hE₀.ne' hd
    (activeOffsets S s r) (measurableSet_sourceDomainOf S s A r E₀ e hB hD)

theorem sourceDomainOf_replaceActive {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (a : Fin q → ℝ) (B : Set (Vector p)) (D : Set (Fin q → ℝ)) :
    sourceDomainOf S s A r E₀ (replaceActive S e a) B D =
      sourceDomainOf S s A r E₀ e B D := by
  ext w
  constructor <;> intro hw <;> refine ⟨hw.1, hw.2.1, ?_⟩ <;> intro f hf hnot
  · simpa only [replaceActive_off S e a f hnot] using hw.2.2 f hf hnot
  · simpa only [replaceActive_off S e a f hnot] using hw.2.2 f hf hnot

theorem imageEventOf_replaceActive_iff {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (a : Fin q → ℝ) (z : Vector p) (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hE₀ : 0 < E₀) (he : ∀ f, 0 < e f) (ha : ∀ i, 0 < a i) :
    (z, E₀, replaceActive S e a) ∈ imageEventOf S s A r B D ↔
      Sum.elim z a ∈ map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomainOf S s A r E₀ e B D := by
  simp only [imageEventOf, Set.mem_setOf_eq, hE₀, replaceActive_pos S e a he ha,
    true_and, replaceActive_at, sourceDomainOf_replaceActive]
  simp

theorem density_mul_ratioWeightOf {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) (g : Vector p → ℝ) (E₀ : ℝ) (e : Face p → ℝ)
    (hE₀ : 0 < E₀) (he : ∀ f, 0 < e f) (y : Coordinates p q)
    (hy : ∀ i, 0 < tube y i) :
    ENNReal.ofReal (standardGaussianDensity p (base y) * Real.exp (-(∑ i, tube y i))) *
        ENNReal.ofReal (ratioWeightOf S s A r B D g
          (base y, E₀, replaceActive S e (tube y))) =
      (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomainOf S s A r E₀ e B D).indicator (fun y =>
          ENNReal.ofReal (pulledDensity S s A r E₀ y *
            g (base (inverse (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) y)))) y := by
  classical
  have hcoord : Sum.elim (base y) (tube y) = y := by
    ext j
    cases j <;> rfl
  have hevent := imageEventOf_replaceActive_iff S s A r E₀ e (tube y) (base y) B D hE₀ he hy
  rw [hcoord] at hevent
  by_cases hmem : y ∈ map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
      sourceDomainOf S s A r E₀ e B D
  · have hze := hevent.mpr hmem
    simp only [ratioWeightOf, Set.indicator_of_mem hze, Set.indicator_of_mem hmem,
      imagePreimage_replaceActive]
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (standardGaussianDensity_pos p (base y)).le (Real.exp_nonneg _))]
    apply congrArg ENNReal.ofReal
    unfold pulledDensity
    field_simp [(standardGaussianDensity_pos p (base y)).ne']
    ring
  · have hze := mt hevent.mp hmem
    simp only [ratioWeightOf, Set.indicator_of_not_mem hze, ENNReal.ofReal_zero,
      mul_zero, Set.indicator_of_not_mem hmem]

theorem lintegral_ratioWeightOf_eq_positive_volume {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (g : Vector p → ℝ) (hgm : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (ratioWeightOf S s A r B D g ze)
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ∫⁻ re, ∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
        (map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
          sourceDomainOf S s A r re.1 re.2 B D).indicator (fun y =>
            ENNReal.ofReal (pulledDensity S s A r re.1 y *
              g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))) y
        ∂volume ∂exponentialRectangleLaw p := by
  rw [lintegral_common_eq_active_volume S _
    (ratioWeightOf_measurable S s A r B D hB hD g hgm hd).ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
  apply setLIntegral_congr_fun (measurableSet_positive_tube p q)
  exact ae_of_all _ fun y hy => density_mul_ratioWeightOf S s A r B D g
    re.1 re.2 hre.1 hre.2 y hy

/-- The actual common Gaussian/exponential expectation equals the Lebesgue
integral on the augmented tube images. The Gaussian density ratio exactly
cancels the output Gaussian density. -/
theorem lintegral_ratioWeightOf_eq_pulledDensity_images {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (g : Vector p → ℝ) (hgm : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (ratioWeightOf S s A r B D g ze)
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ∫⁻ re, ∫⁻ y in map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
          sourceDomainOf S s A r re.1 re.2 B D,
        ENNReal.ofReal (pulledDensity S s A r re.1 y *
          g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))
        ∂volume ∂exponentialRectangleLaw p := by
  rw [lintegral_ratioWeightOf_eq_positive_volume S s A r B D hB hD g hgm hd]
  apply lintegral_congr_ae
  filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
  rw [setLIntegral_indicator
    (measurableSet_image_sourceDomainOf S s A r hre.1 re.2 B D hB hD hd),
    Set.inter_eq_left.mpr (image_map_subset_positive_tube (normalMatrix S A) s.bandwidth hre.1 (activeOffsets S s r) _)]


end
end RectangleCLT.Companion.SignedSurface

import RectangleCLT.GaussianTubeDisintegration
import RectangleCLT.GaussianTubeIntegration
import RectangleCLT.GaussianActiveVolume
import RectangleCLT.GaussianTubeDomination
import RectangleCLT.GaussianTubeImagePositive

/-! Transporting active exponential coordinates into the one common
Gaussian/exponential experiment used to sum disjoint tube images. -/

open MeasureTheory
open scoped ENNReal

namespace RectangleCLT.GaussianTube

noncomputable section

def activeExperiment {p q : ℕ} (S : CompatibleFaceTuple p q)
    (w : (Vector p × ℝ) × ((Face p → ℝ) × (Fin q → ℝ))) :
    Vector p × (ℝ × (Face p → ℝ)) :=
  (w.1.1, w.1.2, replaceActive S w.2.1 w.2.2)

theorem measurePreserving_activeExperiment {p q : ℕ} (S : CompatibleFaceTuple p q)
    (γ : Measure (Vector p)) [SFinite γ] :
    MeasurePreserving (activeExperiment S)
      ((γ.prod unitExponential).prod
        ((faceExponentialLaw p).prod (Measure.pi (fun _ : Fin q => unitExponential))))
      (γ.prod (exponentialRectangleLaw p)) := by
  have hprod := (MeasurePreserving.id (γ.prod unitExponential)).prod
    (measurePreserving_replaceActive S)
  exact (measurePreserving_prodAssoc γ unitExponential (faceExponentialLaw p)).comp hprod

theorem lintegral_common_eq_activeExperiment {p q : ℕ} (S : CompatibleFaceTuple p q)
    (γ : Measure (Vector p)) [SFinite γ]
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂γ.prod (exponentialRectangleLaw p)) =
      ∫⁻ w, H (activeExperiment S w) ∂
        (γ.prod unitExponential).prod
          ((faceExponentialLaw p).prod (Measure.pi (fun _ : Fin q => unitExponential))) := by
  exact ((measurePreserving_activeExperiment S γ).lintegral_comp hH).symm

theorem lintegral_common_eq_active_coordinates {p q : ℕ} (S : CompatibleFaceTuple p q)
    (γ : Measure (Vector p)) [SFinite γ]
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂γ.prod (exponentialRectangleLaw p)) =
      ∫⁻ z, (∫⁻ E₀, (∫⁻ e,
        (∫⁻ a, H (z, E₀, replaceActive S e a)
          ∂Measure.pi (fun _ : Fin q => unitExponential))
        ∂faceExponentialLaw p) ∂unitExponential) ∂γ := by
  rw [lintegral_common_eq_activeExperiment S γ H hH]
  have hm : Measurable
      (fun w : (Vector p × ℝ) × ((Face p → ℝ) × (Fin q → ℝ)) => H (activeExperiment S w)) :=
    hH.comp (measurePreserving_activeExperiment S γ).measurable
  rw [lintegral_prod _ hm.aemeasurable]
  have hsection (v : Vector p × ℝ) :
      Measurable (fun w : (Face p → ℝ) × (Fin q → ℝ) => H (activeExperiment S (v, w))) :=
    (hH.comp (measurePreserving_activeExperiment S γ).measurable).comp
      (measurable_const.prodMk measurable_id)
  have houter : Measurable (fun v : Vector p × ℝ =>
      ∫⁻ w : (Face p → ℝ) × (Fin q → ℝ), H (activeExperiment S (v, w)) ∂
        (faceExponentialLaw p).prod (Measure.pi (fun _ : Fin q => unitExponential))) :=
    by
      have hcur : Measurable (Function.uncurry
          (fun (v : Vector p × ℝ) (w : (Face p → ℝ) × (Fin q → ℝ)) =>
            H (activeExperiment S (v, w)))) := hm
      exact hcur.lintegral_prod_right
  rw [lintegral_prod _ houter.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [] with z
  apply lintegral_congr_ae
  filter_upwards [] with E₀
  simpa only [activeExperiment] using lintegral_prod _ (hsection (z, E₀)).aemeasurable

theorem lintegral_common_eq_replaced_coordinates {p q : ℕ} (S : CompatibleFaceTuple p q)
    (γ : Measure (Vector p)) [SFinite γ]
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂γ.prod (exponentialRectangleLaw p)) =
      ∫⁻ re, (∫⁻ z, (∫⁻ a, H (z, re.1, replaceActive S re.2 a)
        ∂Measure.pi (fun _ : Fin q => unitExponential)) ∂γ) ∂exponentialRectangleLaw p := by
  have hpair : Measurable
      (fun w : (Vector p × (ℝ × (Face p → ℝ))) × (Fin q → ℝ) => (w.1.2.2, w.2)) := by
    fun_prop
  have hnew := (measurePreserving_replaceActive S).measurable.comp hpair
  have harg : Measurable
      (fun w : (Vector p × (ℝ × (Face p → ℝ))) × (Fin q → ℝ) =>
        (w.1.1, w.1.2.1, replaceActive S w.1.2.2 w.2)) := by
    exact (measurable_fst.comp measurable_fst).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk hnew)
  have hcur : Measurable (Function.uncurry
      (fun (zr : Vector p × (ℝ × (Face p → ℝ))) (a : Fin q → ℝ) =>
        H (zr.1, zr.2.1, replaceActive S zr.2.2 a))) := hH.comp harg
  have hG : Measurable (fun zr : Vector p × (ℝ × (Face p → ℝ)) =>
      ∫⁻ a, H (zr.1, zr.2.1, replaceActive S zr.2.2 a)
        ∂Measure.pi (fun _ : Fin q => unitExponential)) := hcur.lintegral_prod_right
  calc
    _ = ∫⁻ z, (∫⁻ re, (∫⁻ a, H (z, re.1, replaceActive S re.2 a)
        ∂Measure.pi (fun _ : Fin q => unitExponential)) ∂exponentialRectangleLaw p) ∂γ := by
      rw [lintegral_common_eq_active_coordinates S γ H hH]
      apply lintegral_congr_ae
      filter_upwards [] with z
      have hm : Measurable (fun re : ℝ × (Face p → ℝ) =>
          ∫⁻ a, H (z, re.1, replaceActive S re.2 a)
            ∂Measure.pi (fun _ : Fin q => unitExponential)) :=
        hG.comp (measurable_const.prodMk measurable_id)
      exact (lintegral_prod _ hm.aemeasurable).symm
    _ = _ := lintegral_lintegral_swap hG.aemeasurable

theorem lintegral_common_eq_active_volume {p q : ℕ} (S : CompatibleFaceTuple p q)
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ∫⁻ re, (∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
        ENNReal.ofReal (standardGaussianDensity p (base y) * Real.exp (-(∑ i, tube y i))) *
          H (base y, re.1, replaceActive S re.2 (tube y))) ∂exponentialRectangleLaw p := by
  rw [lintegral_common_eq_replaced_coordinates S (standardGaussian p) H hH]
  apply lintegral_congr_ae
  filter_upwards [] with re
  have hm : Measurable (fun w : Vector p × (Fin q → ℝ) =>
      H (w.1, re.1, replaceActive S re.2 w.2)) := by
    have hr : Measurable (fun w : Vector p × (Fin q → ℝ) => replaceActive S re.2 w.2) :=
      (measurePreserving_replaceActive S).measurable.comp (measurable_const.prodMk measurable_snd)
    exact hH.comp (measurable_fst.prodMk (measurable_const.prodMk hr))
  exact lintegral_standardGaussian_exponential_eq_volume _ hm

theorem sourceDomain_replaceActive {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (a : Fin q → ℝ) (width : ℝ) :
    sourceDomain S s A r E₀ (replaceActive S e a) width =
      sourceDomain S s A r E₀ e width := by
  ext w
  constructor <;> intro hw <;> refine ⟨hw.1, ?_⟩ <;> intro f hf hnot
  · simpa only [replaceActive_off S e a f hnot] using hw.2 f hf hnot
  · simpa only [replaceActive_off S e a f hnot] using hw.2 f hf hnot

theorem replaceActive_pos {p q : ℕ} (S : CompatibleFaceTuple p q)
    (e : Face p → ℝ) (a : Fin q → ℝ) (he : ∀ f, 0 < e f) (ha : ∀ i, 0 < a i) :
    ∀ f, 0 < replaceActive S e a f := by
  intro f
  classical
  by_cases hf : f ∈ activeFaces S
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hf
    rw [← hi, replaceActive_at]
    exact ha i
  · rw [replaceActive_off S e a f hf]
    exact he f

theorem imageEvent_replaceActive_iff {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (a : Fin q → ℝ) (z : Vector p) (width : ℝ)
    (hE₀ : 0 < E₀) (he : ∀ f, 0 < e f) (ha : ∀ i, 0 < a i) :
    (z, E₀, replaceActive S e a) ∈ imageEvent S s A r width ↔
      Sum.elim z a ∈ map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomain S s A r E₀ e width := by
  simp only [imageEvent, Set.mem_setOf_eq, hE₀, replaceActive_pos S e a he ha,
    true_and, replaceActive_at, sourceDomain_replaceActive]
  simp

theorem imagePreimage_replaceActive {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (y : Coordinates p q) :
    imagePreimage S s A (r, (base y, E₀, replaceActive S e (tube y))) =
      inverse (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) y := by
  unfold imagePreimage
  have hc : Sum.elim (base y) (fun i => replaceActive S e (tube y) (S.face i)) = y := by
    ext j
    cases j <;> simp [base, tube, replaceActive_at]
  rw [hc]

theorem density_mul_imageRatioWeight {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (g : Vector p → ℝ) (E₀ : ℝ) (e : Face p → ℝ)
    (hE₀ : 0 < E₀) (he : ∀ f, 0 < e f) (y : Coordinates p q)
    (hy : ∀ i, 0 < tube y i) :
    ENNReal.ofReal (standardGaussianDensity p (base y) * Real.exp (-(∑ i, tube y i))) *
        ENNReal.ofReal (imageRatioWeight S s A r width g
          (base y, E₀, replaceActive S e (tube y))) =
      (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomain S s A r E₀ e width).indicator (fun y =>
          ENNReal.ofReal (pulledDensity S s A r E₀ y *
            g (base (inverse (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) y)))) y := by
  classical
  have hcoord : Sum.elim (base y) (tube y) = y := by
    ext j
    cases j <;> rfl
  have hevent := imageEvent_replaceActive_iff S s A r E₀ e (tube y) (base y) width hE₀ he hy
  rw [hcoord] at hevent
  by_cases hmem : y ∈ map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
      sourceDomain S s A r E₀ e width
  · have hze := hevent.mpr hmem
    simp only [imageRatioWeight, Set.indicator_of_mem hze, Set.indicator_of_mem hmem,
      imagePreimage_replaceActive]
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (standardGaussianDensity_pos p (base y)).le (Real.exp_nonneg _))]
    apply congrArg ENNReal.ofReal
    unfold pulledDensity
    field_simp [(standardGaussianDensity_pos p (base y)).ne']
    ring
  · have hze := mt hevent.mp hmem
    simp only [imageRatioWeight, Set.indicator_of_not_mem hze, ENNReal.ofReal_zero,
      mul_zero, Set.indicator_of_not_mem hmem]

theorem lintegral_imageRatioWeight_eq_positive_volume {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (g : Vector p → ℝ) (hgm : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (imageRatioWeight S s A r width g ze)
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ∫⁻ re, ∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
        (map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
          sourceDomain S s A r re.1 re.2 width).indicator (fun y =>
            ENNReal.ofReal (pulledDensity S s A r re.1 y *
              g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))) y
        ∂volume ∂exponentialRectangleLaw p := by
  rw [lintegral_common_eq_active_volume S _
    (imageRatioWeight_measurable S s A r width g hgm hd).ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
  apply setLIntegral_congr_fun (measurableSet_positive_tube p q)
  exact ae_of_all _ fun y hy => density_mul_imageRatioWeight S s A r width g
    re.1 re.2 hre.1 hre.2 y hy

/-- The actual common Gaussian/exponential expectation equals the Lebesgue
integral on the augmented tube images. The Gaussian density ratio exactly
cancels the output Gaussian density. -/
theorem lintegral_imageRatioWeight_eq_pulledDensity_images {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (g : Vector p → ℝ) (hgm : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (imageRatioWeight S s A r width g ze)
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ∫⁻ re, ∫⁻ y in map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
          sourceDomain S s A r re.1 re.2 width,
        ENNReal.ofReal (pulledDensity S s A r re.1 y *
          g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))
        ∂volume ∂exponentialRectangleLaw p := by
  rw [lintegral_imageRatioWeight_eq_positive_volume S s A r width g hgm hd]
  apply lintegral_congr_ae
  filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
  rw [setLIntegral_indicator
    (measurableSet_image_sourceDomain S s A r hre.1 re.2 width hd),
    Set.inter_eq_left.mpr (image_sourceDomain_subset_positive_tube S s A r hre.1 re.2 width)]

/-- Exact soft-face normalization in the single common probability experiment
where distinct active face tubes are disjoint. -/
theorem lintegral_imageRatioWeight_eq_softFaceWeight {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z) (hactive : ∀ i, S.face i ∈ s.faces)
    {width : ℝ} (hw : 0 ≤ width)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (imageRatioWeight S s A r width g ze)
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ENNReal.ofReal (width ^ q *
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p) := by
  rw [lintegral_imageRatioWeight_eq_pulledDensity_images S s A r width g hgm hd]
  exact lintegral_pulledDensity_weighted_images S s A r g hgm hgi hg0 hactive hw hd hgram

end

end RectangleCLT.GaussianTube

import RectangleCLTCompanion.SignedSurfaceTransport

/-! The common-experiment transport with an arbitrary positive clock.
In particular, the integer-shape Gamma clocks preserve their exact factors. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def clockRectangleLaw (p : ℕ) (clock : Measure ℝ) : Measure (ℝ × (Face p → ℝ)) :=
  clock.prod (faceExponentialLaw p)

instance clockRectangleLaw_sFinite (p : ℕ) (clock : Measure ℝ) [SFinite clock] :
    SFinite (clockRectangleLaw p clock) := by
  unfold clockRectangleLaw
  infer_instance

instance clockRectangleLaw_probability (p : ℕ) (clock : Measure ℝ) [IsProbabilityMeasure clock] :
    IsProbabilityMeasure (clockRectangleLaw p clock) := by
  unfold clockRectangleLaw
  infer_instance

theorem clockRectangleLaw_ae_pos (p : ℕ) (clock : Measure ℝ) [SFinite clock]
    (hclock : ∀ᵐ t ∂clock, 0 < t) :
    ∀ᵐ e ∂clockRectangleLaw p clock, 0 < e.1 ∧ ∀ f, 0 < e.2 f := by
  exact ((Measure.quasiMeasurePreserving_fst (μ := clock)
    (ν := faceExponentialLaw p)).ae hclock).and
    ((Measure.quasiMeasurePreserving_snd (μ := clock)
      (ν := faceExponentialLaw p)).ae (faceExponentialLaw_ae_pos p))

theorem measurePreserving_activeExperiment_clock {p q : ℕ} (S : CompatibleFaceTuple p q) (clock : Measure ℝ) [SFinite clock]
    (γ : Measure (Vector p)) [SFinite γ] :
    MeasurePreserving (activeExperiment S)
      ((γ.prod clock).prod
        ((faceExponentialLaw p).prod (Measure.pi (fun _ : Fin q => unitExponential))))
      (γ.prod (clockRectangleLaw p clock)) := by
  have hprod := (MeasurePreserving.id (γ.prod clock)).prod
    (measurePreserving_replaceActive S)
  exact (measurePreserving_prodAssoc γ clock (faceExponentialLaw p)).comp hprod

theorem lintegral_common_eq_activeExperiment_clock {p q : ℕ} (S : CompatibleFaceTuple p q) (clock : Measure ℝ) [SFinite clock]
    (γ : Measure (Vector p)) [SFinite γ]
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂γ.prod (clockRectangleLaw p clock)) =
      ∫⁻ w, H (activeExperiment S w) ∂
        (γ.prod clock).prod
          ((faceExponentialLaw p).prod (Measure.pi (fun _ : Fin q => unitExponential))) := by
  exact ((measurePreserving_activeExperiment_clock S clock γ).lintegral_comp hH).symm

theorem lintegral_common_eq_active_coordinates_clock {p q : ℕ} (S : CompatibleFaceTuple p q) (clock : Measure ℝ) [SFinite clock]
    (γ : Measure (Vector p)) [SFinite γ]
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂γ.prod (clockRectangleLaw p clock)) =
      ∫⁻ z, (∫⁻ E₀, (∫⁻ e,
        (∫⁻ a, H (z, E₀, replaceActive S e a)
          ∂Measure.pi (fun _ : Fin q => unitExponential))
        ∂faceExponentialLaw p) ∂clock) ∂γ := by
  rw [lintegral_common_eq_activeExperiment_clock S clock γ H hH]
  have hm : Measurable
      (fun w : (Vector p × ℝ) × ((Face p → ℝ) × (Fin q → ℝ)) => H (activeExperiment S w)) :=
    hH.comp (measurePreserving_activeExperiment_clock S clock γ).measurable
  rw [lintegral_prod _ hm.aemeasurable]
  have hsection (v : Vector p × ℝ) :
      Measurable (fun w : (Face p → ℝ) × (Fin q → ℝ) => H (activeExperiment S (v, w))) :=
    (hH.comp (measurePreserving_activeExperiment_clock S clock γ).measurable).comp
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

theorem lintegral_common_eq_replaced_coordinates_clock {p q : ℕ} (S : CompatibleFaceTuple p q) (clock : Measure ℝ) [SFinite clock]
    (γ : Measure (Vector p)) [SFinite γ]
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂γ.prod (clockRectangleLaw p clock)) =
      ∫⁻ re, (∫⁻ z, (∫⁻ a, H (z, re.1, replaceActive S re.2 a)
        ∂Measure.pi (fun _ : Fin q => unitExponential)) ∂γ) ∂clockRectangleLaw p clock := by
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
        ∂Measure.pi (fun _ : Fin q => unitExponential)) ∂clockRectangleLaw p clock) ∂γ := by
      rw [lintegral_common_eq_active_coordinates_clock S clock γ H hH]
      apply lintegral_congr_ae
      filter_upwards [] with z
      have hm : Measurable (fun re : ℝ × (Face p → ℝ) =>
          ∫⁻ a, H (z, re.1, replaceActive S re.2 a)
            ∂Measure.pi (fun _ : Fin q => unitExponential)) :=
        hG.comp (measurable_const.prodMk measurable_id)
      exact (lintegral_prod _ hm.aemeasurable).symm
    _ = _ := lintegral_lintegral_swap hG.aemeasurable

theorem lintegral_common_eq_active_volume_clock {p q : ℕ} (S : CompatibleFaceTuple p q) (clock : Measure ℝ) [SFinite clock]
    (H : (Vector p × (ℝ × (Face p → ℝ))) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂(standardGaussian p).prod (clockRectangleLaw p clock)) =
      ∫⁻ re, (∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
        ENNReal.ofReal (standardGaussianDensity p (base y) * Real.exp (-(∑ i, tube y i))) *
          H (base y, re.1, replaceActive S re.2 (tube y))) ∂clockRectangleLaw p clock := by
  rw [lintegral_common_eq_replaced_coordinates_clock S clock (standardGaussian p) H hH]
  apply lintegral_congr_ae
  filter_upwards [] with re
  have hm : Measurable (fun w : Vector p × (Fin q → ℝ) =>
      H (w.1, re.1, replaceActive S re.2 w.2)) := by
    have hr : Measurable (fun w : Vector p × (Fin q → ℝ) => replaceActive S re.2 w.2) :=
      (measurePreserving_replaceActive S).measurable.comp (measurable_const.prodMk measurable_snd)
    exact hH.comp (measurable_fst.prodMk (measurable_const.prodMk hr))
  exact lintegral_standardGaussian_exponential_eq_volume _ hm

theorem lintegral_ratioWeightOf_eq_positive_volume_clock {p q : ℕ}
    (S : CompatibleFaceTuple p q) (clock : Measure ℝ) [SFinite clock]
    (hclock : ∀ᵐ t ∂clock, 0 < t) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (g : Vector p → ℝ) (hgm : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (ratioWeightOf S s A r B D g ze)
        ∂(standardGaussian p).prod (clockRectangleLaw p clock)) =
      ∫⁻ re, ∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
        (map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
          sourceDomainOf S s A r re.1 re.2 B D).indicator (fun y =>
            ENNReal.ofReal (pulledDensity S s A r re.1 y *
              g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))) y
        ∂volume ∂clockRectangleLaw p clock := by
  rw [lintegral_common_eq_active_volume_clock S clock _
    (ratioWeightOf_measurable S s A r B D hB hD g hgm hd).ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [clockRectangleLaw_ae_pos p clock hclock] with re hre
  apply setLIntegral_congr_fun (measurableSet_positive_tube p q)
  exact ae_of_all _ fun y hy => density_mul_ratioWeightOf S s A r B D g
    re.1 re.2 hre.1 hre.2 y hy

/-- The actual common Gaussian/exponential expectation equals the Lebesgue
integral on the augmented tube images. The Gaussian density ratio exactly
cancels the output Gaussian density. -/
theorem lintegral_ratioWeightOf_eq_pulledDensity_images_clock {p q : ℕ}
    (S : CompatibleFaceTuple p q) (clock : Measure ℝ) [SFinite clock]
    (hclock : ∀ᵐ t ∂clock, 0 < t) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (g : Vector p → ℝ) (hgm : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (ratioWeightOf S s A r B D g ze)
        ∂(standardGaussian p).prod (clockRectangleLaw p clock)) =
      ∫⁻ re, ∫⁻ y in map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
          sourceDomainOf S s A r re.1 re.2 B D,
        ENNReal.ofReal (pulledDensity S s A r re.1 y *
          g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))
        ∂volume ∂clockRectangleLaw p clock := by
  rw [lintegral_ratioWeightOf_eq_positive_volume_clock S clock hclock s A r B D hB hD g hgm hd]
  apply lintegral_congr_ae
  filter_upwards [clockRectangleLaw_ae_pos p clock hclock] with re hre
  rw [setLIntegral_indicator
    (measurableSet_image_sourceDomainOf S s A r hre.1 re.2 B D hB hD hd),
    Set.inter_eq_left.mpr (image_map_subset_positive_tube (normalMatrix S A) s.bandwidth hre.1 (activeOffsets S s r) _)]


end
end RectangleCLT.Companion.SignedSurface

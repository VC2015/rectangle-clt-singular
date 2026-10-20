import RectangleCLTCompanion.SignedSurfaceTubeDomains
import RectangleCLT.GaussianTubeTransport
import RectangleCLTCompanion.SignedSurfaceTransport

/-! Actual augmented-tube integration on arbitrary measurable coefficient
domains, with an independent measurable restriction on the Gaussian base.
No upper bound on the coefficient coordinates enters the normalization. -/

open MeasureTheory RectangleCLT.GaussianTube Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

theorem sourceDomainOf_iff_inactiveEvent {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (he : ∀ f, 0 < e f)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) (w : Coordinates p q) :
    w ∈ sourceDomainOf S s A r E₀ e B D ↔
      base w ∈ B ∧ tube w ∈ D ∧
        e ∈ inactiveEvent (s.weights (A.mulVec (base w) + r)) (activeFaces S) E₀ := by
  classical
  constructor
  · rintro ⟨hB, hD, hi⟩
    refine ⟨hB, hD, fun f => ?_⟩
    by_cases hf : f ∈ activeFaces S
    · simpa [hf] using he f
    · simp only [hf, ↓reduceIte]
      by_cases hfaces : f ∈ s.faces
      · exact hi f hfaces hf
      · simpa [FaceSmoother.weights, hfaces] using he f
  · rintro ⟨hB, hD, hi⟩
    refine ⟨hB, hD, fun f _ hf => ?_⟩
    have hh := hi f
    simpa only [hf, ↓reduceIte] using hh

/-- The actual pullback Jacobian density, including both domain restrictions. -/
def sourceDensityOf {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (w : Coordinates p q) (re : ℝ × (Face p → ℝ)) : ℝ :=
  ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
      standardGaussianDensity p (base w)) *
    (∏ f ∈ activeFaces S, re.1 * (s.weights (A.mulVec (base w) + r)).weight f) *
    Real.exp (-(activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) * re.1)) *
    (sourceDomainOf S s A r re.1 re.2 B D).indicator (fun _ => (1 : ℝ)) w

theorem sourceDensityOf_eq_sourceKernel {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (w : Coordinates p q) (re : ℝ × (Face p → ℝ)) (he : ∀ f, 0 < re.2 f) :
    sourceDensityOf S s A r B D w re =
      B.indicator (fun _ => (1 : ℝ)) (base w) *
        D.indicator (fun _ => (1 : ℝ)) (tube w) *
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          standardGaussianDensity p (base w)) *
        sourceKernel (s.weights (A.mulVec (base w) + r)) (activeFaces S) re := by
  classical
  have hd := sourceDomainOf_iff_inactiveEvent S s A r re.1 re.2 he B D w
  by_cases hB : base w ∈ B
  · by_cases hD : tube w ∈ D
    · by_cases hi : re.2 ∈ inactiveEvent (s.weights (A.mulVec (base w) + r))
          (activeFaces S) re.1
      · have hw := hd.mpr ⟨hB, hD, hi⟩
        simp only [sourceDensityOf, sourceKernel, Set.indicator_of_mem hw,
          Set.indicator_of_mem hi, Set.indicator_of_mem hB, Set.indicator_of_mem hD,
          one_mul, mul_one]
        ring
      · have hw : w ∉ sourceDomainOf S s A r re.1 re.2 B D := fun h => hi (hd.mp h).2.2
        simp [sourceDensityOf, sourceKernel, Set.indicator_of_not_mem hw,
          Set.indicator_of_not_mem hi]
    · have hw : w ∉ sourceDomainOf S s A r re.1 re.2 B D := fun h => hD (hd.mp h).2.1
      simp [sourceDensityOf, Set.indicator_of_not_mem hw, Set.indicator_of_not_mem hD]
  · have hw : w ∉ sourceDomainOf S s A r re.1 re.2 B D := fun h => hB (hd.mp h).1
    simp [sourceDensityOf, Set.indicator_of_not_mem hw, Set.indicator_of_not_mem hB]

theorem sourceDensityOf_integral_exponentials {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) (w : Coordinates p q) :
    (∫ re, sourceDensityOf S s A r B D w re ∂exponentialRectangleLaw p) =
      B.indicator (fun _ => (1 : ℝ)) (base w) * D.indicator (fun _ => (1 : ℝ)) (tube w) *
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          standardGaussianDensity p (base w)) * (q.factorial : ℝ) *
        s.softFaceWeight (activeFaces S) (A.mulVec (base w) + r) := by
  calc
    _ = ∫ re,
        B.indicator (fun _ => (1 : ℝ)) (base w) * D.indicator (fun _ => (1 : ℝ)) (tube w) *
          ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
            standardGaussianDensity p (base w)) *
          sourceKernel (s.weights (A.mulVec (base w) + r)) (activeFaces S) re
        ∂exponentialRectangleLaw p := by
      apply integral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
      exact sourceDensityOf_eq_sourceKernel S s A r B D w re hre.2
    _ = _ := by
      rw [integral_const_mul, sourceKernel_integral, activeFaces_card]
      unfold FaceSmoother.softFaceWeight FaceSmoother.F
      ring

theorem sourceDensityOf_integrable_exponentials {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) (w : Coordinates p q) :
    Integrable (sourceDensityOf S s A r B D w) (exponentialRectangleLaw p) := by
  apply ((sourceKernel_integrable (s.weights (A.mulVec (base w) + r))
    (activeFaces S)).const_mul _).congr
  filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
  exact (sourceDensityOf_eq_sourceKernel S s A r B D w re hre.2).symm

theorem sourceDensityOf_nonneg {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (w : Coordinates p q) (re : ℝ × (Face p → ℝ)) (hr : 0 ≤ re.1)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    0 ≤ sourceDensityOf S s A r B D w re := by
  unfold sourceDensityOf
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (div_nonneg hgram (pow_nonneg s.bandwidth_pos.le _))
      (standardGaussianDensity_pos p _).le)
    (Finset.prod_nonneg (fun f _ => mul_nonneg hr ((s.weights _).nonneg f))))
    (Real.exp_nonneg _)) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem sourceDensityOf_measurable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hB : MeasurableSet B) (hD : MeasurableSet D) :
    Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      sourceDensityOf S s A r B D z.1 z.2) := by
  classical
  let E : Set (Coordinates p q × (ℝ × (Face p → ℝ))) :=
    {z | z.1 ∈ sourceDomainOf S s A r z.2.1 z.2.2 B D}
  have hb : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) => base z.1) :=
    measurable_base_projection.comp measurable_fst
  have ht : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) => tube z.1) :=
    measurable_tube_projection.comp measurable_fst
  have hW := ((measurable_mulVec A).comp hb).add_const r
  have hclock : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) => z.2.1) := by fun_prop
  have hE : MeasurableSet E := by
    change MeasurableSet {z : Coordinates p q × (ℝ × (Face p → ℝ)) |
      base z.1 ∈ B ∧ tube z.1 ∈ D ∧ ∀ f ∈ s.faces, f ∉ activeFaces S →
        z.2.1 * (s.weights (A.mulVec (base z.1) + r)).weight f < z.2.2 f}
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (hB.preimage hb).inter ((hD.preimage ht).inter ?_)
    exact MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => measurableSet_lt
        (hclock.mul ((s.continuous_weight f).measurable.comp hW)) (by fun_prop))))
  have hweights (f : Face p) : Measurable
      (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
        (s.weights (A.mulVec (base z.1) + r)).weight f) :=
    (s.continuous_weight f).measurable.comp hW
  have hmass : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      activeMass (s.weights (A.mulVec (base z.1) + r)) (activeFaces S)) :=
    Finset.measurable_sum _ (fun f _ => hweights f)
  have hfun : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        standardGaussianDensity p (base z.1)) *
      (∏ f ∈ activeFaces S, z.2.1 * (s.weights (A.mulVec (base z.1) + r)).weight f) *
      Real.exp (-(activeMass (s.weights (A.mulVec (base z.1) + r)) (activeFaces S) * z.2.1))) :=
    ((standardGaussianDensity_measurable p).comp hb).const_mul _ |>.mul
      (Finset.measurable_prod _ (fun f _ => hclock.mul (hweights f))) |>.mul
        (hmass.mul hclock).neg.exp
  convert hfun.indicator hE using 1
  funext z
  by_cases hz : z ∈ E
  · have hz' : z.1 ∈ sourceDomainOf S s A r z.2.1 z.2.2 B D := hz
    simp only [sourceDensityOf, Set.indicator_of_mem hz, Set.indicator_of_mem hz', mul_one]
  · have hz' : z.1 ∉ sourceDomainOf S s A r z.2.1 z.2.2 B D := hz
    simp only [sourceDensityOf, Set.indicator_of_not_mem hz, Set.indicator_of_not_mem hz', mul_zero]

/-- Splitting augmented Lebesgue coordinates gives exactly the coefficient
domain's measure. This nonnegative identity permits infinite-volume domains. -/
theorem lintegral_domain_mul {p q : ℕ} {D : Set (Fin q → ℝ)} (hD : MeasurableSet D)
    (f : Vector p → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w : Coordinates p q,
      D.indicator (fun _ => (1 : ℝ≥0∞)) (tube w) * f (base w)) =
      volume D * ∫⁻ z, f z := by
  have hDind : Measurable (D.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hD
  let F : Vector p × (Fin q → ℝ) → ℝ≥0∞ := fun z =>
    f z.1 * D.indicator (fun _ => (1 : ℝ≥0∞)) z.2
  have hF : Measurable F := (hf.comp measurable_fst).mul (hDind.comp measurable_snd)
  have hsplit := (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin p ⊕ Fin q => ℝ)).lintegral_comp hF
  calc
    _ = ∫⁻ w : Coordinates p q, F (base w, tube w) := by
      congr 1
      funext w
      exact mul_comm _ _
    _ = ∫⁻ z : Vector p × (Fin q → ℝ), F z ∂volume.prod volume := hsplit
    _ = _ := by
      rw [lintegral_prod_mul hf.aemeasurable hDind.aemeasurable,
        lintegral_indicator hD, setLIntegral_one, mul_comm]

theorem lintegral_pulledDensity_weighted_imageOf_eq_sourceDensityOf {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (g : Vector p → ℝ)
    (hactive : ∀ i, S.face i ∈ s.faces) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (e : Face p → ℝ) {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ y in GaussianTube.map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomainOf S s A r E₀ e B D,
      ENNReal.ofReal (pulledDensity S s A r E₀ y *
        g (base (inverse (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) y)))) =
      ∫⁻ w, ENNReal.ofReal (sourceDensityOf S s A r B D w (E₀, e) * g (base w)) := by
  rw [lintegral_image_map _ s.bandwidth_pos hE₀ hd _ hgram
    (measurableSet_sourceDomainOf S s A r E₀ e hB hD)]
  rw [← lintegral_indicator (measurableSet_sourceDomainOf S s A r E₀ e hB hD)]
  apply lintegral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ sourceDomainOf S s A r E₀ e B D
  · rw [Set.indicator_of_mem hw]
    have hi := inverse_map (normalMatrix S A) s.bandwidth_pos.ne' hE₀.ne' hd
      (activeOffsets S s r) w
    have hp : (∏ i, tube (GaussianTube.map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        ∏ f ∈ activeFaces S, E₀ * (s.weights (A.mulVec (base w) + r)).weight f := by
      rw [activeFaces_prod]
      exact Finset.prod_congr rfl (fun i _ => activeExponential_eq S s A r hactive E₀ w i)
    have hs : (∑ i, tube (GaussianTube.map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) * E₀ := by
      simp only [activeMass, activeFaces_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [activeExponential_eq S s A r hactive E₀ w i, mul_comm])
    have hj : 0 ≤ ((∏ i, tube (GaussianTube.map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) / s.bandwidth ^ q) *
          ((normalMatrix S A).transpose * normalMatrix S A).det :=
      mul_nonneg (div_nonneg (Finset.prod_nonneg (fun i _ =>
        (tube_map_pos _ _ hE₀ _ _ _).le)) (pow_nonneg s.bandwidth_pos.le _)) hgram
    rw [← ENNReal.ofReal_mul hj]
    simp only [pulledDensity, hi, hp, hs, sourceDensityOf, Set.indicator_of_mem hw, mul_one]
    congr 1
    ring
  · simp only [Set.indicator_of_not_mem hw, sourceDensityOf, mul_zero, zero_mul,
      ENNReal.ofReal_zero]

/-- Complete actual image integration for arbitrary measurable base and
coefficient domains. The coefficient volume remains an `ENNReal`, so even
an unbounded, infinite-volume coefficient domain is allowed. -/
theorem lintegral_pulledDensity_weighted_imagesOf {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z) (hactive : ∀ i, S.face i ∈ s.faces)
    {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ re, ∫⁻ y in GaussianTube.map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
        sourceDomainOf S s A r re.1 re.2 B D,
      ENNReal.ofReal (pulledDensity S s A r re.1 y *
        g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))
        ∂volume ∂exponentialRectangleLaw p) =
      volume D * ENNReal.ofReal
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          (q.factorial : ℝ) *
          ∫ z in B, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z
            ∂standardGaussian p) := by
  let C := (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
    (q.factorial : ℝ)
  let F : Vector p → ℝ := B.indicator (fun z => C *
    (standardGaussianDensity p z * (s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z)))
  have hC : 0 ≤ C := mul_nonneg
    (div_nonneg hgram (pow_nonneg s.bandwidth_pos.le _)) (by positivity)
  have hW : Measurable (fun z : Vector p => A.mulVec z + r) := (measurable_mulVec A).add_const r
  have hsoft : Measurable (fun z : Vector p =>
      s.softFaceWeight (activeFaces S) (A.mulVec z + r)) :=
    (s.continuous_softFaceWeight _).measurable.comp hW
  have hFi : Integrable F := by
    have hi := hgi.bdd_mul hsoft.aestronglyMeasurable ⟨1, fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg _ _)]
      exact s.softFaceWeight_le_one _ _⟩
    exact (((standardGaussian_integrable_density_mul_iff _).mp hi).const_mul C).indicator hB
  have hFm : Measurable F :=
    (((standardGaussianDensity_measurable p).mul (hsoft.mul hgm)).const_mul C).indicator hB
  have hF0 (z : Vector p) : 0 ≤ F z := Set.indicator_nonneg
    (fun z _ => mul_nonneg hC (mul_nonneg (standardGaussianDensity_pos p z).le
      (mul_nonneg (s.softFaceWeight_nonneg _ _) (hg0 z)))) z
  have hFint : (∫ z, F z) = C *
      ∫ z in B, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p := by
    calc
      _ = C * ∫ z, standardGaussianDensity p z *
          B.indicator (fun z => s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z) z := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ B <;> simp [F, hz]
      _ = _ := by rw [← standardGaussian_integral_density_mul, integral_indicator hB]
  have hm : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      sourceDensityOf S s A r B D z.1 z.2 * g (base z.1)) :=
    (sourceDensityOf_measurable S s A r hB hD).mul
      (hgm.comp (measurable_base_projection.comp measurable_fst))
  have hinner (w : Coordinates p q) :
      (∫⁻ re, ENNReal.ofReal (sourceDensityOf S s A r B D w re * g (base w))
        ∂exponentialRectangleLaw p) =
      D.indicator (fun _ => (1 : ℝ≥0∞)) (tube w) * ENNReal.ofReal (F (base w)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((sourceDensityOf_integrable_exponentials S s A r B D w).mul_const (g (base w)))
      (by
        filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
        exact mul_nonneg (sourceDensityOf_nonneg S s A r B D w re hre.1.le hgram) (hg0 _)),
      integral_mul_const, sourceDensityOf_integral_exponentials]
    by_cases hwD : tube w ∈ D
    · by_cases hwB : base w ∈ B
      · simp only [Set.indicator_of_mem hwD, Set.indicator_of_mem hwB, one_mul]
        dsimp only [F]
        rw [Set.indicator_of_mem hwB]
        congr 1
        dsimp only [C]
        ring
      · simp [F, hwB, hwD]
    · simp [hwD]
  calc
    _ = ∫⁻ re, ∫⁻ w, ENNReal.ofReal (sourceDensityOf S s A r B D w re * g (base w))
        ∂volume ∂exponentialRectangleLaw p := by
      apply lintegral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
      exact lintegral_pulledDensity_weighted_imageOf_eq_sourceDensityOf
        S s A r g hactive hre.1 re.2 hB hD hd hgram
    _ = ∫⁻ w, ∫⁻ re, ENNReal.ofReal (sourceDensityOf S s A r B D w re * g (base w))
        ∂exponentialRectangleLaw p := (lintegral_lintegral_swap hm.ennreal_ofReal.aemeasurable).symm
    _ = ∫⁻ w : Coordinates p q,
        D.indicator (fun _ => (1 : ℝ≥0∞)) (tube w) * ENNReal.ofReal (F (base w)) := by
      apply lintegral_congr_ae
      exact ae_of_all _ hinner
    _ = volume D * ENNReal.ofReal (∫ z, F z) := by
      rw [lintegral_domain_mul hD _ hFm.ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF0)]
    _ = _ := by rw [hFint]

/-- The complete common Gaussian/exponential experiment has exactly the
soft-face normalization, including the arbitrary coefficient volume. -/
theorem lintegral_ratioWeightOf_eq_softFaceWeight {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z) (hactive : ∀ i, S.face i ∈ s.faces)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (ratioWeightOf S s A r B D g ze)
      ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      volume D * ENNReal.ofReal
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          (q.factorial : ℝ) *
          ∫ z in B, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z
            ∂standardGaussian p) := by
  rw [lintegral_ratioWeightOf_eq_pulledDensity_images S s A r B D hB hD g hgm hd]
  exact lintegral_pulledDensity_weighted_imagesOf S s A r g hgm hgi hg0 hactive hB hD hd hgram

end

end RectangleCLT.Companion.SignedSurface

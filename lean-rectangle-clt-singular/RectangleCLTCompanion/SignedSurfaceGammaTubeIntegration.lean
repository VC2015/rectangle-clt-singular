import RectangleCLTCompanion.SignedSurfaceTubeIntegration
import RectangleCLTCompanion.SignedSurfaceClockTransport
import RectangleCLTCompanion.GammaMixture

/-! Exact integer-shape Gamma normalization of augmented surface tubes.
The retained rising factorial is essential when applying the identities to
natural powers of the smoother. -/

open MeasureTheory ProbabilityTheory RectangleCLT.GaussianTube Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion

noncomputable section

private theorem gammaClock_pdf_nat (a : ℕ) (t : ℝ) :
    gammaPDFReal ((a : ℝ) + 1) 1 t =
      if 0 ≤ t then (a.factorial : ℝ)⁻¹ * t ^ a * Real.exp (-t) else 0 := by
  unfold gammaPDFReal
  simp only [Real.one_rpow, Real.Gamma_nat_eq_factorial, add_sub_cancel_right,
    Real.rpow_natCast, one_mul, one_div]

theorem gammaClock_integral_eq_Ioi (a : ℕ) (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaClock a) =
      (a.factorial : ℝ)⁻¹ * ∫ t in Ioi 0, t ^ a * Real.exp (-t) * f t := by
  unfold gammaClock gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal ((a : ℝ) + 1) 1).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [gammaPDF, ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg (by positivity : 0 < (a : ℝ) + 1) (by norm_num : (0 : ℝ) < 1) _),
    smul_eq_mul]
  have heq : (fun t : ℝ => gammaPDFReal ((a : ℝ) + 1) 1 t * f t) =
      (Ici (0 : ℝ)).indicator
        (fun t => (a.factorial : ℝ)⁻¹ * (t ^ a * Real.exp (-t) * f t)) := by
    funext t
    rw [gammaClock_pdf_nat]
    simp only [Set.indicator, mem_Ici]
    split_ifs <;> simp [mul_assoc]
  rw [heq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul]

theorem gammaClock_integrable_iff_Ioi (a : ℕ) (f : ℝ → ℝ) :
    Integrable f (gammaClock a) ↔
      IntegrableOn (fun t => (a.factorial : ℝ)⁻¹ *
        (t ^ a * Real.exp (-t) * f t)) (Ioi 0) := by
  unfold gammaClock gammaMeasure gammaPDF
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gammaPDFReal ((a : ℝ) + 1) 1).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [gammaPDF, ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg (by positivity : 0 < (a : ℝ) + 1) (by norm_num : (0 : ℝ) < 1) _),
    smul_eq_mul]
  have heq : (fun t : ℝ => gammaPDFReal ((a : ℝ) + 1) 1 t * f t) =
      (Ici (0 : ℝ)).indicator
        (fun t => (a.factorial : ℝ)⁻¹ * (t ^ a * Real.exp (-t) * f t)) := by
    funext t
    rw [gammaClock_pdf_nat]
    simp only [Set.indicator, mem_Ici]
    split_ifs <;> simp [mul_assoc]
  rw [heq, integrable_indicator_iff measurableSet_Ici]
  exact ⟨fun h => h.congr_set_ae Ioi_ae_eq_Ici,
    fun h => h.congr_set_ae Ioi_ae_eq_Ici.symm⟩

/-- The exact Gamma-clock polynomial Laplace transform. -/
theorem gammaClock_integral_pow_mul_exp (a q : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t, t ^ q * Real.exp (-T * t) ∂gammaClock a) =
      ((a + q).factorial : ℝ) / (a.factorial : ℝ) / (1 + T) ^ (a + q + 1) := by
  rw [gammaClock_integral_eq_Ioi]
  have heq : (fun t : ℝ => t ^ a * Real.exp (-t) * (t ^ q * Real.exp (-T * t))) =
      (fun t : ℝ => t ^ (a + q) * Real.exp (-((1 + T) * t))) := by
    funext t
    rw [pow_add]
    rw [show t ^ a * Real.exp (-t) * (t ^ q * Real.exp (-T * t)) =
      (t ^ a * t ^ q) * (Real.exp (-t) * Real.exp (-T * t)) by ring,
      ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_natPow_mul_exp_neg_one_add_Ioi (a + q) hT]
  ring

theorem gammaClock_integrable_pow_mul_exp (a q : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun t => t ^ q * Real.exp (-T * t)) (gammaClock a) := by
  apply (gammaClock_integrable_iff_Ioi a _).mpr
  apply ((integrableOn_natPow_mul_exp_neg_mul_Ioi (a + q)
    (show 0 < 1 + T by linarith)).const_mul (a.factorial : ℝ)⁻¹).congr
  filter_upwards [] with t
  congr 1
  rw [pow_add]
  rw [show -((1 + T) * t) = -t + -T * t by ring, Real.exp_add]
  ring

namespace SignedSurface

/-- The Gamma normalization retained by an active face set. -/
def gammaFaceKernel {p : ℕ} (a : ℕ) (w : FaceWeights p) (S : Finset (Face p)) : ℝ :=
  w.F ^ (a + 1) * ∏ f ∈ S, w.pi f

theorem sourceKernel_integrable_gamma {p : ℕ} (a : ℕ) (w : FaceWeights p)
    (S : Finset (Face p)) : Integrable (sourceKernel w S) (gammaRectangleLaw p a) := by
  apply (integrable_prod_iff (sourceKernel_measurable w S).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (sourceKernel_integrable_inner w S), ?_⟩
  apply ((gammaClock_integrable_pow_mul_exp a S.card w.T_nonneg).const_mul
    (∏ f ∈ S, w.weight f)).congr
  filter_upwards [gammaClock_ae_pos a] with t ht
  calc
    (∏ f ∈ S, w.weight f) * (t ^ S.card * Real.exp (-w.T * t)) =
        ∫ e, sourceKernel w S (t, e) ∂faceExponentialLaw p := by
      rw [sourceKernel_integral_inner w S ht.le]
      simp only [Finset.prod_mul_distrib, Finset.prod_const]
      rw [neg_mul]
      ring
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun e => by
        change sourceKernel w S (t, e) = ‖sourceKernel w S (t, e)‖
        rw [Real.norm_eq_abs, abs_of_nonneg (sourceKernel_nonneg w S ht.le e)]

theorem sourceKernel_integral_gamma {p : ℕ} (a : ℕ) (w : FaceWeights p)
    (S : Finset (Face p)) :
    (∫ re, sourceKernel w S re ∂gammaRectangleLaw p a) =
      ((a + S.card).factorial : ℝ) / (a.factorial : ℝ) * gammaFaceKernel a w S := by
  rw [gammaRectangleLaw, integral_prod _ (sourceKernel_integrable_gamma a w S)]
  calc
    _ = (∏ f ∈ S, w.weight f) *
        ∫ t, t ^ S.card * Real.exp (-w.T * t) ∂gammaClock a := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [gammaClock_ae_pos a] with t ht
      rw [sourceKernel_integral_inner w S ht.le]
      simp only [Finset.prod_mul_distrib, Finset.prod_const]
      rw [neg_mul]
      ring
    _ = _ := by
      rw [gammaClock_integral_pow_mul_exp a S.card w.T_nonneg]
      unfold gammaFaceKernel FaceWeights.F FaceWeights.pi
      rw [Finset.prod_div_distrib, Finset.prod_const, div_pow]
      rw [show a + S.card + 1 = (a + 1) + S.card by omega, pow_add]
      field_simp
      ring


theorem gammaFaceKernel_nonneg {p : ℕ} (a : ℕ) (w : FaceWeights p)
    (S : Finset (Face p)) : 0 ≤ gammaFaceKernel a w S :=
  mul_nonneg (pow_nonneg w.F_pos.le _) (Finset.prod_nonneg fun f _ => w.pi_nonneg f)

theorem gammaFaceKernel_le_one {p : ℕ} (a : ℕ) (w : FaceWeights p)
    (S : Finset (Face p)) : gammaFaceKernel a w S ≤ 1 := by
  have hprod : (∏ f ∈ S, w.pi f) ≤ 1 := Finset.prod_le_one
    (fun f _ => w.pi_nonneg f) (fun f _ => (w.pi_le_theta f).trans w.theta_lt_one.le)
  exact (mul_le_mul_of_nonneg_left hprod (pow_nonneg w.F_pos.le _)).trans
    (by simpa using pow_le_one₀ w.F_pos.le w.F_le_one (n := a + 1))

@[fun_prop] theorem continuous_gammaFaceKernel {p : ℕ} (s : FaceSmoother p)
    (a : ℕ) (S : Finset (Face p)) :
    Continuous (fun x => gammaFaceKernel a (s.weights x) S) :=
  (s.continuous_F.pow (a + 1)).mul
    (continuous_finset_prod S (fun f _ => s.continuous_pi f))

theorem sourceDensityOf_integral_gamma {p q : ℕ} (a : ℕ) (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) (w : Coordinates p q) :
    (∫ re, sourceDensityOf S s A r B D w re ∂gammaRectangleLaw p a) =
      B.indicator (fun _ => (1 : ℝ)) (base w) * D.indicator (fun _ => (1 : ℝ)) (tube w) *
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          standardGaussianDensity p (base w)) * (((a + q).factorial : ℝ) / (a.factorial : ℝ)) *
        gammaFaceKernel a (s.weights (A.mulVec (base w) + r)) (activeFaces S) := by
  calc
    _ = ∫ re,
        B.indicator (fun _ => (1 : ℝ)) (base w) * D.indicator (fun _ => (1 : ℝ)) (tube w) *
          ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
            standardGaussianDensity p (base w)) *
          sourceKernel (s.weights (A.mulVec (base w) + r)) (activeFaces S) re
        ∂gammaRectangleLaw p a := by
      apply integral_congr_ae
      filter_upwards [gammaRectangleLaw_ae_pos p a] with re hre
      exact sourceDensityOf_eq_sourceKernel S s A r B D w re hre.2
    _ = _ := by
      rw [integral_const_mul, sourceKernel_integral_gamma, activeFaces_card]
      ring

theorem sourceDensityOf_integrable_gamma {p q : ℕ} (a : ℕ) (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) (w : Coordinates p q) :
    Integrable (sourceDensityOf S s A r B D w) (gammaRectangleLaw p a) := by
  apply ((sourceKernel_integrable_gamma a (s.weights (A.mulVec (base w) + r))
    (activeFaces S)).const_mul _).congr
  filter_upwards [gammaRectangleLaw_ae_pos p a] with re hre
  exact (sourceDensityOf_eq_sourceKernel S s A r B D w re hre.2).symm

theorem lintegral_pulledDensity_weighted_imagesOf_gamma {p q : ℕ}
    (a : ℕ) (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
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
        ∂volume ∂gammaRectangleLaw p a) =
      volume D * ENNReal.ofReal
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          (((a + q).factorial : ℝ) / (a.factorial : ℝ)) *
          ∫ z in B, gammaFaceKernel a (s.weights (A.mulVec z + r)) (activeFaces S) * g z
            ∂standardGaussian p) := by
  let C := (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
    (((a + q).factorial : ℝ) / (a.factorial : ℝ))
  let F : Vector p → ℝ := B.indicator (fun z => C *
    (standardGaussianDensity p z * (gammaFaceKernel a (s.weights (A.mulVec z + r)) (activeFaces S) * g z)))
  have hC : 0 ≤ C := mul_nonneg
    (div_nonneg hgram (pow_nonneg s.bandwidth_pos.le _)) (by positivity)
  have hW : Measurable (fun z : Vector p => A.mulVec z + r) := (measurable_mulVec A).add_const r
  have hsoft : Measurable (fun z : Vector p =>
      gammaFaceKernel a (s.weights (A.mulVec z + r)) (activeFaces S)) :=
    (continuous_gammaFaceKernel s a _).measurable.comp hW
  have hFi : Integrable F := by
    have hi := hgi.bdd_mul hsoft.aestronglyMeasurable ⟨1, fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gammaFaceKernel_nonneg a _ _)]
      exact gammaFaceKernel_le_one a _ _⟩
    exact (((standardGaussian_integrable_density_mul_iff _).mp hi).const_mul C).indicator hB
  have hFm : Measurable F :=
    (((standardGaussianDensity_measurable p).mul (hsoft.mul hgm)).const_mul C).indicator hB
  have hF0 (z : Vector p) : 0 ≤ F z := Set.indicator_nonneg
    (fun z _ => mul_nonneg hC (mul_nonneg (standardGaussianDensity_pos p z).le
      (mul_nonneg (gammaFaceKernel_nonneg a _ _) (hg0 z)))) z
  have hFint : (∫ z, F z) = C *
      ∫ z in B, gammaFaceKernel a (s.weights (A.mulVec z + r)) (activeFaces S) * g z ∂standardGaussian p := by
    calc
      _ = C * ∫ z, standardGaussianDensity p z *
          B.indicator (fun z => gammaFaceKernel a (s.weights (A.mulVec z + r)) (activeFaces S) * g z) z := by
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
        ∂gammaRectangleLaw p a) =
      D.indicator (fun _ => (1 : ℝ≥0∞)) (tube w) * ENNReal.ofReal (F (base w)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((sourceDensityOf_integrable_gamma a S s A r B D w).mul_const (g (base w)))
      (by
        filter_upwards [gammaRectangleLaw_ae_pos p a] with re hre
        exact mul_nonneg (sourceDensityOf_nonneg S s A r B D w re hre.1.le hgram) (hg0 _)),
      integral_mul_const, sourceDensityOf_integral_gamma a]
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
        ∂volume ∂gammaRectangleLaw p a := by
      apply lintegral_congr_ae
      filter_upwards [gammaRectangleLaw_ae_pos p a] with re hre
      exact lintegral_pulledDensity_weighted_imageOf_eq_sourceDensityOf
        S s A r g hactive hre.1 re.2 hB hD hd hgram
    _ = ∫⁻ w, ∫⁻ re, ENNReal.ofReal (sourceDensityOf S s A r B D w re * g (base w))
        ∂gammaRectangleLaw p a := (lintegral_lintegral_swap hm.ennreal_ofReal.aemeasurable).symm
    _ = ∫⁻ w : Coordinates p q,
        D.indicator (fun _ => (1 : ℝ≥0∞)) (tube w) * ENNReal.ofReal (F (base w)) := by
      apply lintegral_congr_ae
      exact ae_of_all _ hinner
    _ = volume D * ENNReal.ofReal (∫ z, F z) := by
      rw [lintegral_domain_mul hD _ hFm.ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF0)]
    _ = _ := by rw [hFint]



/-- Actual Gamma-clock tube identity in the common Gaussian and exponential
experiment. The factors `(a+q)!/a!` are retained exactly. -/
theorem lintegral_ratioWeightOf_eq_gammaFaceKernel {p q : ℕ}
    (a : ℕ) (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z) (hactive : ∀ i, S.face i ∈ s.faces)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (ratioWeightOf S s A r B D g ze)
      ∂(standardGaussian p).prod (gammaRectangleLaw p a)) =
      volume D * ENNReal.ofReal
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          (((a + q).factorial : ℝ) / (a.factorial : ℝ)) *
          ∫ z in B, gammaFaceKernel a (s.weights (A.mulVec z + r)) (activeFaces S) * g z
            ∂standardGaussian p) := by
  rw [show gammaRectangleLaw p a = clockRectangleLaw p (gammaClock a) from rfl,
    lintegral_ratioWeightOf_eq_pulledDensity_images_clock S (gammaClock a)
      (gammaClock_ae_pos a) s A r B D hB hD g hgm hd]
  exact lintegral_pulledDensity_weighted_imagesOf_gamma a S s A r g hgm hgi hg0
    hactive hB hD hd hgram

theorem gamma_face_factor_one (a : ℕ) :
    ((a + 1).factorial : ℝ) / (a.factorial : ℝ) = (a : ℝ) + 1 := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero a)

theorem gamma_face_factor_two (a : ℕ) :
    ((a + 2).factorial : ℝ) / (a.factorial : ℝ) =
      ((a : ℝ) + 1) * ((a : ℝ) + 2) := by
  rw [show a + 2 = (a + 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
    mul_div_assoc, gamma_face_factor_one]
  push_cast
  ring

end SignedSurface
end
end RectangleCLT.Companion

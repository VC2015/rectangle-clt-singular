import RectangleCLTArxivV1.SupplementalHMixedCoareaLipschitz
import RectangleCLTArxivV1.PositiveMixedCoareaTests

/-! Uniform positive first-density and mixed increment budgets. The
constants are independent of thresholds and sampled bases. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def positiveMixedGaussianPeak : ℝ := (Real.sqrt (2*Real.pi))⁻¹
def positiveMixedMassBudget : ℝ := positiveMixedGaussianPeak^2
def positiveMixedPlaneBudget : ℝ := 4*positiveMixedGaussianPeak^2

theorem positiveMixedGaussianPeak_nonneg : 0≤positiveMixedGaussianPeak := by
  unfold positiveMixedGaussianPeak
  positivity

theorem positiveMixedMassBudget_nonneg : 0≤positiveMixedMassBudget := sq_nonneg _
theorem positiveMixedPlaneBudget_nonneg : 0≤positiveMixedPlaneBudget := by
  unfold positiveMixedPlaneBudget
  positivity

theorem gaussianPDFReal_le_positiveMixedGaussianPeak (a : ℝ) :
    gaussianPDFReal 0 1 a≤positiveMixedGaussianPeak := by
  have he : gaussianPDFReal 0 1 a=positiveMixedGaussianPeak*Real.exp (-(a^2/2)) := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,neg_div,positiveMixedGaussianPeak]
  rw [he]
  exact (mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg a])) positiveMixedGaussianPeak_nonneg).trans_eq
      (mul_one _)

theorem gaussianPDFReal_sq_le_positiveMixedGaussianPeak (a : ℝ) :
    gaussianPDFReal 0 1 a*a^2≤2*positiveMixedGaussianPeak := by
  have he : gaussianPDFReal 0 1 a=positiveMixedGaussianPeak*Real.exp (-(a^2/2)) := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,neg_div,positiveMixedGaussianPeak]
  have hh := mul_le_mul_of_nonneg_left (gaussian_exp_sq_polynomial_bound a 2 (by norm_num))
    positiveMixedGaussianPeak_nonneg
  rw [he]
  nlinarith

theorem gaussianPDFReal_pair_le_positiveMixedMassBudget (a c : ℝ) :
    gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c≤positiveMixedMassBudget := by
  exact (mul_le_mul (gaussianPDFReal_le_positiveMixedGaussianPeak a)
    (gaussianPDFReal_le_positiveMixedGaussianPeak c) (gaussianPDFReal_nonneg _ _ _)
    positiveMixedGaussianPeak_nonneg).trans_eq (by unfold positiveMixedMassBudget; ring)

theorem gaussianPDFReal_pair_normSq_le_positiveMixedPlaneBudget (a c : ℝ) :
    gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c*(a^2+c^2)≤positiveMixedPlaneBudget := by
  have ha := (mul_le_mul_of_nonneg_right (gaussianPDFReal_sq_le_positiveMixedGaussianPeak a)
    (gaussianPDFReal_nonneg 0 1 c)).trans
      (mul_le_mul_of_nonneg_left (gaussianPDFReal_le_positiveMixedGaussianPeak c)
        (mul_nonneg (by norm_num) positiveMixedGaussianPeak_nonneg))
  have hc := (mul_le_mul_of_nonneg_left (gaussianPDFReal_sq_le_positiveMixedGaussianPeak c)
    (gaussianPDFReal_nonneg 0 1 a)).trans
      (mul_le_mul_of_nonneg_right (gaussianPDFReal_le_positiveMixedGaussianPeak a)
        (mul_nonneg (by norm_num) positiveMixedGaussianPeak_nonneg))
  unfold positiveMixedPlaneBudget
  nlinarith

theorem gaussianFiniteWeightedThreshold_one_bounds {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) :
    0≤gaussianFiniteWeightedThreshold s u b (fun _ => (1:ℝ)) ∧
      gaussianFiniteWeightedThreshold s u b (fun _ => (1:ℝ))≤1 := by
  have hm := measurableSet_gaussianFiniteThresholdEvent s u b
  have hi : Integrable (fun g : Vector r =>
      (gaussianFiniteThresholdEvent s u b).indicator (fun _ => (1:ℝ)) g) (standardGaussian r) :=
    (integrable_const _).indicator hm
  constructor
  · exact integral_nonneg (fun g => by by_cases hg : g∈gaussianFiniteThresholdEvent s u b <;> simp [hg])
  · have hh := integral_mono hi (integrable_const (μ := standardGaussian r) (1:ℝ))
      (fun g => by by_cases hg : g∈gaussianFiniteThresholdEvent s u b <;> simp [hg])
    simpa only [integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul] using hh

theorem gaussianFiniteWeightedThreshold_plane_bounds {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (q : Vector r) (a : ℝ) :
    0≤gaussianFiniteWeightedThreshold s u b (fun g => a^2+faceDot q g^2) ∧
      gaussianFiniteWeightedThreshold s u b (fun g => a^2+faceDot q g^2)≤a^2+vectorNormSq q := by
  have hm := measurableSet_gaussianFiniteThresholdEvent s u b
  have hi : Integrable (fun g : Vector r => a^2+faceDot q g^2) (standardGaussian r) :=
    (integrable_const _).add (standardGaussian_integrable_faceDot_sq q)
  have hp (g : Vector r) : 0≤a^2+faceDot q g^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · exact integral_nonneg (fun g => by by_cases hg : g∈gaussianFiniteThresholdEvent s u b <;> simp [hg,hp g])
  · have hh := integral_mono (hi.indicator hm) hi (fun g => by
      by_cases hg : g∈gaussianFiniteThresholdEvent s u b
      · simp only [indicator_of_mem hg,le_refl]
      · simp only [indicator_of_not_mem hg]
        exact hp g)
    rw [integral_add (integrable_const _) (standardGaussian_integrable_faceDot_sq q),
      integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul,standardGaussian_integral_faceDot_sq] at hh
    exact hh

theorem measurable_gaussianFiniteWeightedThreshold_parameter {α : Type*} [MeasurableSpace α]
    {m r : ℕ} (s : Finset (Fin m)) (u : Fin m → Vector r)
    (B : α → Vector m) (hB : Measurable B) (F : α × Vector r → ℝ) (hF : Measurable F) :
    Measurable (fun a => gaussianFiniteWeightedThreshold s u (B a) (fun g => F (a,g))) := by
  let E := {z : α × Vector r | ∀ k∈s,faceDot (u k) z.2≤B z.1 k}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((continuous_faceDot_left (u k)).measurable.comp measurable_snd)
      ((measurable_pi_apply k).comp (hB.comp measurable_fst))
  exact ((hF.indicator hE).stronglyMeasurable.integral_prod_right').measurable

theorem positiveMixed_iic_increment_bound (H : ℝ → ℝ) (hHi : Integrable H volume)
    (C : ℝ) (hH : ∀ t,‖H t‖≤C) {ν : ℝ} (hν : 0<ν) (a c d : ℝ) :
    ‖(∫ t in Iic ((c-a)/ν),H t)-(∫ t in Iic ((d-a)/ν),H t)‖≤(C/ν)*|c-d| := by
  rw [intervalIntegral.integral_Iic_sub_Iic hHi.integrableOn hHi.integrableOn]
  have hh : ‖∫ t in (d-a)/ν..(c-a)/ν,H t‖≤C*abs ((c-a)/ν-(d-a)/ν) :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hH t)
  apply hh.trans_eq
  rw [show (c-a)/ν-(d-a)/ν=(c-d)/ν by ring,abs_div,abs_of_pos hν]
  ring

theorem measurable_positiveMixedFirstMassDensity {m r : ℕ} (u : Fin m → Vector r) (j : Fin m) :
    Measurable (fun b => positiveMixedFirstMassDensity u b j) := by
  unfold positiveMixedFirstMassDensity
  apply ((measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply j)).mul
  exact measurable_gaussianFiniteWeightedThreshold_parameter _ _ _
    (by apply measurable_pi_lambda; intro k; exact (measurable_pi_apply k).sub ((measurable_pi_apply j).mul_const _))
    (fun _ => (1:ℝ)) measurable_const

theorem measurable_positiveMixedFirstPlaneDensity {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) :
    Measurable (fun b => positiveMixedFirstPlaneDensity u b j l) := by
  unfold positiveMixedFirstPlaneDensity
  apply ((measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply j)).mul
  unfold positiveMixedPlaneFacetWeight
  exact measurable_gaussianFiniteWeightedThreshold_parameter (Finset.univ.erase j)
    (fun k => gaussianNormalProjection (u j) (u k))
    (fun b : Vector m => fun k => b k-b j*faceDot (u k) (u j))
    (by apply measurable_pi_lambda; intro k; exact (measurable_pi_apply k).sub ((measurable_pi_apply j).mul_const _))
    (fun z : Vector m × Vector r => (z.1 j)^2+faceDot (gaussianPairConditionalDirection u j l) z.2^2)
    ((((measurable_pi_apply j).comp measurable_fst).pow_const 2).add
      (((continuous_faceDot_left (gaussianPairConditionalDirection u j l)).measurable.comp measurable_snd).pow_const 2))

theorem positiveMixedFirstMassDensity_bounds {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) :
    0≤positiveMixedFirstMassDensity u b j ∧ positiveMixedFirstMassDensity u b j≤positiveMixedGaussianPeak := by
  have hprob := gaussianFiniteWeightedThreshold_one_bounds (Finset.univ.erase j)
    (fun k => gaussianNormalProjection (u j) (u k)) (fun k => b k-b j*faceDot (u k) (u j))
  constructor
  · exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) hprob.1
  · exact (mul_le_mul_of_nonneg_left hprob.2 (gaussianPDFReal_nonneg _ _ _)).trans
      (by simpa only [mul_one] using gaussianPDFReal_le_positiveMixedGaussianPeak (b j))

theorem positiveMixedFirstMassDensity_norm_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) :
    ‖positiveMixedFirstMassDensity u b j‖≤positiveMixedGaussianPeak := by
  rw [Real.norm_eq_abs,abs_of_nonneg (positiveMixedFirstMassDensity_bounds u b j).1]
  exact (positiveMixedFirstMassDensity_bounds u b j).2

theorem positiveMixedFirstPlaneDensity_bounds {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    0≤positiveMixedFirstPlaneDensity u b j l ∧
      positiveMixedFirstPlaneDensity u b j l≤3*positiveMixedGaussianPeak := by
  have hq := (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).1
  have hb := gaussianFiniteWeightedThreshold_plane_bounds (Finset.univ.erase j)
    (fun k => gaussianNormalProjection (u j) (u k)) (fun k => b k-b j*faceDot (u k) (u j))
      (gaussianPairConditionalDirection u j l) (b j)
  constructor
  · exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) hb.1
  · have h := mul_le_mul_of_nonneg_left hb.2 (gaussianPDFReal_nonneg 0 1 (b j))
    rw [hq] at h
    have h1 := gaussianPDFReal_le_positiveMixedGaussianPeak (b j)
    have h2 := gaussianPDFReal_sq_le_positiveMixedGaussianPeak (b j)
    change gaussianPDFReal 0 1 (b j)*_≤_
    exact h.trans (by nlinarith)

theorem positiveMixedFirstPlaneDensity_norm_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    ‖positiveMixedFirstPlaneDensity u b j l‖≤3*positiveMixedGaussianPeak := by
  rw [Real.norm_eq_abs,abs_of_nonneg (positiveMixedFirstPlaneDensity_bounds u b j l hu hv hp hm).1]
  exact (positiveMixedFirstPlaneDensity_bounds u b j l hu hv hp hm).2

theorem hardGaussianPairSectionProbability_bounds {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e q : Vector r) (a t : ℝ) :
    0≤hardGaussianPairSectionProbability s u b e q a t ∧
      hardGaussianPairSectionProbability s u b e q a t≤1 := by
  rw [← gaussianFiniteWeightedSection_one_eq_pairProbability,
    gaussianFiniteWeightedSection_one_eq_sectionProbability]
  unfold gaussianThresholdSectionProbability
  rw [← gaussianFiniteWeightedThreshold_one_eq_cdf]
  exact gaussianFiniteWeightedThreshold_one_bounds _ _ _

private theorem positiveMixed_residualLevels_update {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l) (z : ℝ) :
    (fun k => Function.update b l z k-Function.update b l z j*faceDot (u k) (u j))=
      Function.update (fun k => b k-b j*faceDot (u k) (u j)) l (z-b j*faceDot (u l) (u j)) := by
  classical
  funext k
  rw [Function.update_of_ne hjl]
  by_cases hkl : k=l
  · subst k
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hkl]

private theorem positiveMixed_section_plane_eq_pairProbability {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (e q : Vector r)
    (hq : vectorNormSq q=1) (a t : ℝ) :
    gaussianFiniteWeightedSection s (fun k => gaussianNormalProjection e (u k))
      (fun k => b k-a*faceDot (u k) e) q (positiveMixedPlaneFacetWeight q a) t=
      (a^2+t^2)*hardGaussianPairSectionProbability s u b e q a t := by
  rw [gaussianFiniteWeightedSection_plane_eq_probability _ _ _ q hq a t,
    ← gaussianFiniteWeightedSection_one_eq_sectionProbability,
    gaussianFiniteWeightedSection_one_eq_pairProbability]

theorem positiveMixedFirstMassDensity_update_eq_section_integral {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (z : ℝ) :
    positiveMixedFirstMassDensity u (Function.update b l z) j=
      ∫ t in Iic ((z-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l),
        gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*
          hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b (u j)
            (gaussianPairConditionalDirection u j l) (b j) t) := by
  classical
  obtain ⟨hq,_,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  have hul : gaussianNormalProjection (u j) (u l)=
      gaussianThresholdResidualScale u j l • gaussianPairConditionalDirection u j l := by
    rw [gaussianPairConditionalDirection,smul_smul,mul_inv_cancel₀ hν.ne',one_smul]
  unfold positiveMixedFirstMassDensity
  rw [positiveMixed_residualLevels_update u b j l hjl z,Function.update_of_ne hjl,
    gaussianFiniteWeightedThreshold_update_eq_section_integral _ _ _ l
      (Finset.mem_erase.mpr ⟨hjl.symm,Finset.mem_univ _⟩) _ hq hν hul _ measurable_const
      (integrable_const _) ,←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by dsimp only; rw [gaussianFiniteWeightedSection_one_eq_pairProbability])

theorem positiveMixedFirstPlaneDensity_update_eq_section_integral {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (z : ℝ) :
    positiveMixedFirstPlaneDensity u (Function.update b l z) j l=
      ∫ t in Iic ((z-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l),
        gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*((b j)^2+t^2)*
          hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b (u j)
            (gaussianPairConditionalDirection u j l) (b j) t) := by
  classical
  obtain ⟨hq,_,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  have hul : gaussianNormalProjection (u j) (u l)=
      gaussianThresholdResidualScale u j l • gaussianPairConditionalDirection u j l := by
    rw [gaussianPairConditionalDirection,smul_smul,mul_inv_cancel₀ hν.ne',one_smul]
  unfold positiveMixedFirstPlaneDensity
  rw [positiveMixed_residualLevels_update u b j l hjl z,Function.update_of_ne hjl,
    gaussianFiniteWeightedThreshold_update_eq_section_integral _ _ _ l
      (Finset.mem_erase.mpr ⟨hjl.symm,Finset.mem_univ _⟩) _ hq hν hul _
      (measurable_positiveMixedPlaneFacetWeight _ _) (integrable_positiveMixedPlaneFacetWeight _ _),
    ←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    dsimp only
    rw [positiveMixed_section_plane_eq_pairProbability _ u b _ _ hq]
    ring)

theorem positiveMixedFirstMassDensity_update_increment_bound {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (c d : ℝ) :
    ‖positiveMixedFirstMassDensity u (Function.update b l c) j-
      positiveMixedFirstMassDensity u (Function.update b l d) j‖≤
      (positiveMixedMassBudget/gaussianThresholdResidualScale u j l)*|c-d| := by
  obtain ⟨hq,_,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  let H := fun t => gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*
    hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b (u j)
      (gaussianPairConditionalDirection u j l) (b j) t)
  have hi : Integrable H volume := by
    have hh := (standardRealGaussian_integrable_density_mul (integrable_gaussianFiniteWeightedSection
      ((Finset.univ.erase j).erase l) (fun k => gaussianNormalProjection (u j) (u k))
      (fun k => b k-b j*faceDot (u k) (u j)) (gaussianPairConditionalDirection u j l) hq
      (fun _ => 1) measurable_const (integrable_const _))).const_mul (gaussianPDFReal 0 1 (b j))
    simpa only [gaussianFiniteWeightedSection_one_eq_pairProbability] using hh
  have hH (t : ℝ) : ‖H t‖≤positiveMixedMassBudget := by
    have hprob := hardGaussianPairSectionProbability_bounds ((Finset.univ.erase j).erase l) u b
      (u j) (gaussianPairConditionalDirection u j l) (b j) t
    have hpdf : 0≤gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 t :=
      mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
      (mul_nonneg (gaussianPDFReal_nonneg _ _ _) hprob.1))]
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hprob.2 hpdf).trans
      (by simpa only [mul_one] using gaussianPDFReal_pair_le_positiveMixedMassBudget (b j) t)
  rw [positiveMixedFirstMassDensity_update_eq_section_integral u b j l hjl hu hv hp hm c,
    positiveMixedFirstMassDensity_update_eq_section_integral u b j l hjl hu hv hp hm d]
  exact positiveMixed_iic_increment_bound H hi positiveMixedMassBudget hH hν _ c d

theorem positiveMixedFirstPlaneDensity_update_increment_bound {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (c d : ℝ) :
    ‖positiveMixedFirstPlaneDensity u (Function.update b l c) j l-
      positiveMixedFirstPlaneDensity u (Function.update b l d) j l‖≤
      (positiveMixedPlaneBudget/gaussianThresholdResidualScale u j l)*|c-d| := by
  obtain ⟨hq,_,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  let H := fun t => gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*((b j)^2+t^2)*
    hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b (u j)
      (gaussianPairConditionalDirection u j l) (b j) t)
  have hi : Integrable H volume := by
    have hh := (standardRealGaussian_integrable_density_mul (integrable_gaussianFiniteWeightedSection
      ((Finset.univ.erase j).erase l) (fun k => gaussianNormalProjection (u j) (u k))
      (fun k => b k-b j*faceDot (u k) (u j)) (gaussianPairConditionalDirection u j l) hq
      (positiveMixedPlaneFacetWeight (gaussianPairConditionalDirection u j l) (b j))
      (measurable_positiveMixedPlaneFacetWeight _ _) (integrable_positiveMixedPlaneFacetWeight _ _))).const_mul
        (gaussianPDFReal 0 1 (b j))
    have he (t : ℝ) : gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*
        gaussianFiniteWeightedSection ((Finset.univ.erase j).erase l)
          (fun k => gaussianNormalProjection (u j) (u k)) (fun k => b k-b j*faceDot (u k) (u j))
          (gaussianPairConditionalDirection u j l)
          (positiveMixedPlaneFacetWeight (gaussianPairConditionalDirection u j l) (b j)) t)=H t := by
      rw [positiveMixed_section_plane_eq_pairProbability _ u b _ _ hq]
      dsimp only [H]
      ring
    exact hh.congr (ae_of_all _ he)
  have hH (t : ℝ) : ‖H t‖≤positiveMixedPlaneBudget := by
    have hprob := hardGaussianPairSectionProbability_bounds ((Finset.univ.erase j).erase l) u b
      (u j) (gaussianPairConditionalDirection u j l) (b j) t
    have hpdf : 0≤gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 t*((b j)^2+t^2) :=
      mul_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
      (mul_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hprob.1))]
    have hh := mul_le_mul_of_nonneg_left hprob.2 hpdf
    simpa only [mul_assoc] using hh.trans
      (by simpa only [mul_one] using gaussianPDFReal_pair_normSq_le_positiveMixedPlaneBudget (b j) t)
  rw [positiveMixedFirstPlaneDensity_update_eq_section_integral u b j l hjl hu hv hp hm c,
    positiveMixedFirstPlaneDensity_update_eq_section_integral u b j l hjl hu hv hp hm d]
  exact positiveMixed_iic_increment_bound H hi positiveMixedPlaneBudget hH hν _ c d

theorem lipschitzWith_positiveMixedFirstMassDensity_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    LipschitzWith ⟨positiveMixedMassBudget/gaussianThresholdResidualScale u j l,
      div_nonneg positiveMixedMassBudget_nonneg (by unfold gaussianThresholdResidualScale; positivity)⟩
      (fun c => positiveMixedFirstMassDensity u (Function.update b l c) j) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [dist_eq_norm,Real.norm_eq_abs] using
    positiveMixedFirstMassDensity_update_increment_bound u b j l hjl hu hv hp hm c d

theorem lipschitzWith_positiveMixedFirstPlaneDensity_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    LipschitzWith ⟨positiveMixedPlaneBudget/gaussianThresholdResidualScale u j l,
      div_nonneg positiveMixedPlaneBudget_nonneg (by unfold gaussianThresholdResidualScale; positivity)⟩
      (fun c => positiveMixedFirstPlaneDensity u (Function.update b l c) j l) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [dist_eq_norm,Real.norm_eq_abs] using
    positiveMixedFirstPlaneDensity_update_increment_bound u b j l hjl hu hv hp hm c d

end
end RectangleCLTArxivV1

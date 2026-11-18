import RectangleCLTArxivV1.PositiveMixedCoareaTests
import RectangleCLTArxivV1.SupplementalHWeightedGammaPrimitive

/-! First hard Gaussian coarea for the positive mass and actual plane
quadratic tests, supplying the genuine primitives for Gamma exchange. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def positiveGaussianPlaneTest {r : ℕ} (e q : Vector r) (g : Vector r) : ℝ :=
  faceDot e g^2+faceDot q g^2

theorem measurable_positiveGaussianPlaneTest {r : ℕ} (e q : Vector r) :
    Measurable (positiveGaussianPlaneTest e q) :=
  ((continuous_faceDot_left e).measurable.pow_const 2).add ((continuous_faceDot_left q).measurable.pow_const 2)

theorem integrable_positiveGaussianPlaneTest {r : ℕ} (e q : Vector r) :
    Integrable (positiveGaussianPlaneTest e q) (standardGaussian r) :=
  (standardGaussian_integrable_faceDot_sq e).add (standardGaussian_integrable_faceDot_sq q)

theorem integral_positiveGaussianPlaneTest {r : ℕ} (e q : Vector r)
    (he : vectorNormSq e=1) (hq : vectorNormSq q=1) :
    (∫ g,|positiveGaussianPlaneTest e q g| ∂standardGaussian r)=2 := by
  have hp (g : Vector r) : 0≤positiveGaussianPlaneTest e q g := add_nonneg (sq_nonneg _) (sq_nonneg _)
  simp_rw [abs_of_nonneg (hp _)]
  unfold positiveGaussianPlaneTest
  rw [integral_add (standardGaussian_integrable_faceDot_sq e)
    (standardGaussian_integrable_faceDot_sq q),standardGaussian_integral_faceDot_sq,
    standardGaussian_integral_faceDot_sq,he,hq]
  norm_num

theorem positiveGaussianPlaneTest_eq_actual_projection {m r : ℕ} (u : Fin m → Vector r)
    (j l : Fin m) (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (g : Vector r) :
    positiveGaussianPlaneTest (u j) (gaussianPairConditionalDirection u j l) g=
      vectorNormSq ((supplementalHPairPlane (u j) (u l)).mulVec g) := by
  rw [supplementalHPairPlane_normSq _ _ _ hu hv (positiveMixed_pair_gram_pos u j l hu hv hp hm),
    ← gaussianPairConditionalDirection_eq_referenceComplement u j l hu hv]
  rfl

theorem gaussianFiniteWeightedSection_planeTest_eq {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (e q : Vector r)
    (he : vectorNormSq e=1) (heq : faceDot e q=0) (t : ℝ) :
    gaussianFiniteWeightedSection s u b e (positiveGaussianPlaneTest e q) t=
      gaussianFiniteWeightedThreshold s (fun k => gaussianNormalProjection e (u k))
        (fun k => b k-t*faceDot (u k) e) (positiveMixedPlaneFacetWeight q t) := by
  unfold gaussianFiniteWeightedSection gaussianFiniteWeightedThreshold
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    have hiff : gaussianSectionPoint e t g∈gaussianFiniteThresholdEvent s u b ↔
        g∈gaussianFiniteThresholdEvent s (fun k => gaussianNormalProjection e (u k))
          (fun k => b k-t*faceDot (u k) e) := by
      constructor <;> intro h k hk
      · have hh := h k hk
        rw [gaussianSectionPoint_faceDot] at hh
        change faceDot (gaussianNormalProjection e (u k)) g≤b k-t*faceDot (u k) e
        linarith
      · have hh := h k hk
        rw [gaussianSectionPoint_faceDot]
        dsimp only at hh
        linarith
    by_cases hg : g∈gaussianFiniteThresholdEvent s (fun k => gaussianNormalProjection e (u k))
        (fun k => b k-t*faceDot (u k) e)
    · rw [indicator_of_mem (hiff.mpr hg),indicator_of_mem hg]
      unfold positiveGaussianPlaneTest positiveMixedPlaneFacetWeight
      rw [gaussianSectionPoint_on_hyperplane e t he]
      have hq : faceDot q (gaussianSectionPoint e t g)=faceDot q g := by
        rw [gaussianSectionPoint_eq,threshold_faceDot_add_right,threshold_faceDot_smul_right,
          faceDot_comm q e,heq,mul_zero,add_zero]
      rw [hq]
    · rw [indicator_of_not_mem (fun h => hg (hiff.mp h)),indicator_of_not_mem hg])

theorem continuousAt_gaussianFiniteWeightedSection_planeTest_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (e q : Vector r)
    (he : vectorNormSq e=1) (heq : faceDot e q=0) (t : ℝ)
    (hreg : ∀ k∈s,gaussianNormalProjection e (u k)≠0 ∨ b k-t*faceDot (u k) e≠0) :
    ContinuousAt (gaussianFiniteWeightedSection s u b e (positiveGaussianPlaneTest e q)) t := by
  let v := fun k => gaussianNormalProjection e (u k)
  let c := fun z : ℝ => fun k => b k-z*faceDot (u k) e
  let F := fun g => faceDot q g^2
  have hFi : Integrable F (standardGaussian r) := standardGaussian_integrable_faceDot_sq q
  have hFm : Measurable F := (continuous_faceDot_left q).measurable.pow_const 2
  have hc : Continuous c := by fun_prop
  have hfun : gaussianFiniteWeightedSection s u b e (positiveGaussianPlaneTest e q)=fun z =>
      (∫ g,(gaussianFiniteThresholdEvent s v (c z)).indicator F g ∂standardGaussian r)+
      z^2*gaussianFiniteThresholdCDF s v (c z) := by
    funext z
    rw [gaussianFiniteWeightedSection_planeTest_eq s u b e q he heq z,
      gaussianFiniteThresholdCDF_eq_integral,←integral_const_mul,
      ←integral_add (hFi.indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _))
        (((integrable_const (1:ℝ)).indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _)).const_mul _)]
    unfold gaussianFiniteWeightedThreshold
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      dsimp only
      by_cases hg : g∈gaussianFiniteThresholdEvent s v (c z)
      · rw [indicator_of_mem hg,indicator_of_mem hg,indicator_of_mem hg]
        unfold positiveMixedPlaneFacetWeight F
        ring
      · rw [indicator_of_not_mem hg,indicator_of_not_mem hg,indicator_of_not_mem hg,mul_zero,add_zero])
  rw [hfun]
  exact ((continuousAt_weighted_gaussianFiniteThreshold_of_slack s v (c t) hreg F hFm hFi).comp hc.continuousAt).add
    ((continuousAt_id.pow 2).mul ((continuousAt_gaussianFiniteThresholdCDF_of_slack s v (c t) hreg).comp hc.continuousAt))

/-- Actual first coarea for the plane moment test. All original
inequalities remain in the true hard primitive and section. -/
theorem hasDerivAt_positivePlaneThreshold_update_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : ∀ k∈Finset.univ.erase j,gaussianNormalProjection (u j) (u k)≠0 ∨
      b k-b j*faceDot (u k) (u j)≠0) :
    HasDerivAt (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z)
      (positiveGaussianPlaneTest (u j) (gaussianPairConditionalDirection u j l)))
      (positiveMixedFirstPlaneDensity u b j l) (b j) := by
  have hg := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  have hc := continuousAt_gaussianFiniteWeightedSection_planeTest_of_slack (Finset.univ.erase j) u b
    (u j) (gaussianPairConditionalDirection u j l) hu hg.2.1 (b j) hreg
  have hd := hasDerivAt_gaussianFiniteWeightedThreshold_update Finset.univ u b j (Finset.mem_univ _)
    (u j) hu (show (0:ℝ)<1 by norm_num) (by simp)
    (positiveGaussianPlaneTest (u j) (gaussianPairConditionalDirection u j l))
    (measurable_positiveGaussianPlaneTest _ _) (integrable_positiveGaussianPlaneTest _ _) (b j)
    (by simpa only [div_one] using hc)
  simpa only [div_one,gaussianFiniteWeightedSection_planeTest_eq _ _ _ _ _ hu hg.2.1] using hd

end
end RectangleCLTArxivV1

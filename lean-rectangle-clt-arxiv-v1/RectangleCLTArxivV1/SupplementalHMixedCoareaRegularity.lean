import RectangleCLTArxivV1.SupplementalHMixedCoareaIntegral

/-! The actual signed first-facet score has a continuous remaining
Gaussian section at ordinary double-residual slack. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def gaussianFacetScore {r : ℕ} (e : Vector r) (a : ℝ) (g : Vector r) : ℝ :=
  vectorNormSq (gaussianSectionPoint e a g)-(r:ℝ)

theorem measurable_gaussianFacetScore {r : ℕ} (e : Vector r) (a : ℝ) :
    Measurable (gaussianFacetScore e a) := by
  have hg : Measurable (gaussianSectionPoint e a) :=
    (measurable_gaussianNormalSectionMap e).comp (measurable_const.prodMk measurable_id)
  exact (Finset.measurable_sum _ (fun k _ => ((measurable_pi_apply k).comp hg).pow_const 2)).sub_const _

theorem integrable_gaussianFacetScore {r : ℕ} (e : Vector r)
    (he : vectorNormSq e=1) (a : ℝ) : Integrable (gaussianFacetScore e a) (standardGaussian r) := by
  unfold gaussianFacetScore
  simp_rw [vectorNormSq_gaussianSectionPoint e a he]
  exact ((((standardGaussian_integrable_vectorNormSq _).sub
    (standardGaussian_integrable_faceDot_sq e)).add (integrable_const (a^2))).sub (integrable_const _))

theorem gaussianFiniteWeightedSection_score_eq {m n : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector (n+1)) (b : Vector m) (e q : Vector (n+1))
    (he : vectorNormSq e=1) (hq : vectorNormSq q=1) (heq : faceDot e q=0)
    (a t : ℝ) :
    gaussianFiniteWeightedSection s u b q (gaussianFacetScore e a) t=
      (∫ g,(gaussianFiniteThresholdEvent s (fun k => gaussianNormalProjection q (u k))
        (fun k => b k-t*faceDot (u k) q)).indicator
          (fun g => vectorNormSq (gaussianPairSectionPoint e q a 0 g)-((n+1:ℕ):ℝ)) g
            ∂standardGaussian (n+1))+
      t^2*gaussianFiniteThresholdCDF s (fun k => gaussianNormalProjection q (u k))
        (fun k => b k-t*faceDot (u k) q) := by
  let v := fun k => gaussianNormalProjection q (u k)
  let c := fun k => b k-t*faceDot (u k) q
  let f := fun g => vectorNormSq (gaussianPairSectionPoint e q a 0 g)-((n+1:ℕ):ℝ)
  have hfi : Integrable f (standardGaussian (n+1)) := by
    dsimp only [f]
    simp_rw [vectorNormSq_gaussianPairSectionPoint e q he hq heq]
    exact ((((((standardGaussian_integrable_vectorNormSq _).sub
      (standardGaussian_integrable_faceDot_sq e)).sub (standardGaussian_integrable_faceDot_sq q)).add
        (integrable_const (a^2))).add (integrable_const (0^2:ℝ))).sub (integrable_const _))
  rw [gaussianFiniteThresholdCDF_eq_integral,← integral_const_mul,
    ← integral_add (hfi.indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _))
      (((integrable_const (1:ℝ)).indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _)).const_mul _)]
  unfold gaussianFiniteWeightedSection
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    have hiff : gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent s u b ↔
        g∈gaussianFiniteThresholdEvent s v c := by
      constructor <;> intro h k hk
      · have hh := h k hk
        rw [gaussianSectionPoint_faceDot] at hh
        change faceDot (gaussianNormalProjection q (u k)) g≤b k-t*faceDot (u k) q
        linarith
      · have hh := h k hk
        rw [gaussianSectionPoint_faceDot]
        change faceDot (gaussianNormalProjection q (u k)) g≤b k-t*faceDot (u k) q at hh
        linarith
    by_cases hg : g∈gaussianFiniteThresholdEvent s v c
    · rw [indicator_of_mem (hiff.mpr hg),indicator_of_mem hg,indicator_of_mem hg]
      change vectorNormSq (gaussianPairSectionPoint e q a t g)-((n+1:ℕ):ℝ)=
        (vectorNormSq (gaussianPairSectionPoint e q a 0 g)-((n+1:ℕ):ℝ))+t^2*1
      rw [vectorNormSq_gaussianPairSectionPoint e q he hq heq,
        vectorNormSq_gaussianPairSectionPoint e q he hq heq]
      ring
    · rw [indicator_of_not_mem (fun h => hg (hiff.mp h)),indicator_of_not_mem hg,indicator_of_not_mem hg,mul_zero,add_zero])

/-- Local weighted section continuity is proved by a fixed integrable
quadratic majorant and ordinary residual boundary nullity. -/
theorem continuousAt_gaussianFiniteWeightedSection_score_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e q : Vector (n+1)) (he : vectorNormSq e=1) (hq : vectorNormSq q=1)
    (heq : faceDot e q=0) (a t : ℝ)
    (hreg : ∀ k∈s,gaussianNormalProjection q (u k)≠0 ∨ b k-t*faceDot (u k) q≠0) :
    ContinuousAt (gaussianFiniteWeightedSection s u b q (gaussianFacetScore e a)) t := by
  let v := fun k => gaussianNormalProjection q (u k)
  let c := fun z : ℝ => fun k => b k-z*faceDot (u k) q
  let f := fun g => vectorNormSq (gaussianPairSectionPoint e q a 0 g)-((n+1:ℕ):ℝ)
  have hf : Measurable f := by
    exact (measurable_gaussianFacetScore e a).comp
      ((measurable_gaussianNormalSectionMap q).comp (measurable_const.prodMk measurable_id))
  have hfi : Integrable f (standardGaussian (n+1)) := by
    dsimp only [f]
    simp_rw [vectorNormSq_gaussianPairSectionPoint e q he hq heq]
    exact ((((((standardGaussian_integrable_vectorNormSq _).sub
      (standardGaussian_integrable_faceDot_sq e)).sub (standardGaussian_integrable_faceDot_sq q)).add
        (integrable_const (a^2))).add (integrable_const (0^2:ℝ))).sub (integrable_const _))
  have hc : Continuous c := by fun_prop
  have hefun : gaussianFiniteWeightedSection s u b q (gaussianFacetScore e a)=fun z =>
      (∫ g,(gaussianFiniteThresholdEvent s v (c z)).indicator f g ∂standardGaussian (n+1))+
        z^2*gaussianFiniteThresholdCDF s v (c z) :=
    funext (gaussianFiniteWeightedSection_score_eq s u b e q he hq heq a)
  rw [hefun]
  exact ((continuousAt_weighted_gaussianFiniteThreshold_of_slack s v (c t) hreg f hf hfi).comp hc.continuousAt).add
    ((continuousAt_id.pow 2).mul
      ((continuousAt_gaussianFiniteThresholdCDF_of_slack s v (c t) hreg).comp hc.continuousAt))

end
end RectangleCLTArxivV1

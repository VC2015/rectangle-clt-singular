import RectangleCLTArxivV1.PositiveFirstCoarea

/-! Actual first positive mass/plane derivatives at volume-almost every
threshold, with arbitrary dependent normal families. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped Topology
noncomputable section

theorem hasDerivAt_positiveMassThreshold_update_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1)
    (hreg : ∀ k∈Finset.univ.erase j,gaussianNormalProjection (u j) (u k)≠0 ∨
      b k-b j*faceDot (u k) (u j)≠0) :
    HasDerivAt (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z) (fun _ => 1))
      (positiveMixedFirstMassDensity u b j) (b j) := by
  have hc := continuousAt_gaussianThresholdSectionProbability_of_slack (Finset.univ.erase j) u b (u j) (b j) hreg
  have hc' : ContinuousAt (gaussianFiniteWeightedSection (Finset.univ.erase j) u b (u j) (fun _ => 1)) (b j) := by
    convert hc using 1
    funext t
    exact gaussianFiniteWeightedSection_one_eq_sectionProbability _ _ _ _ t
  have hd := hasDerivAt_gaussianFiniteWeightedThreshold_update Finset.univ u b j (Finset.mem_univ _)
    (u j) hu (show (0:ℝ)<1 by norm_num) (by simp) (fun _ => 1) measurable_const (integrable_const _) (b j)
    (by simpa only [div_one] using hc')
  simpa only [div_one,gaussianFiniteWeightedSection_one_eq_sectionProbability,positiveMixedFirstMassDensity,
    gaussianFiniteWeightedThreshold_one_eq_cdf,gaussianThresholdSectionProbability] using hd

theorem ae_hasDerivAt_positiveMassThreshold_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1) (j : Fin m) :
    ∀ᵐ b : Vector m ∂volume,
      HasDerivAt (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z) (fun _ => 1))
        (positiveMixedFirstMassDensity u b j) (b j) := by
  filter_upwards [ae_localThresholdRegularity u] with b hb
  exact hasDerivAt_positiveMassThreshold_update_of_slack u b j (hu j)
    (fun k hk => hb j k (Finset.mem_erase.mp hk).1)

theorem ae_hasDerivAt_positivePlaneThreshold_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1) (j l : Fin m)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    ∀ᵐ b : Vector m ∂volume,
      HasDerivAt (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z)
        (positiveGaussianPlaneTest (u j) (gaussianPairConditionalDirection u j l)))
        (positiveMixedFirstPlaneDensity u b j l) (b j) := by
  filter_upwards [ae_localThresholdRegularity u] with b hb
  exact hasDerivAt_positivePlaneThreshold_update_of_slack u b j l (hu j) (hu l) hp hm
    (fun k hk => hb j k (Finset.mem_erase.mp hk).1)

end
end RectangleCLTArxivV1

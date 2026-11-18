import RectangleCLTArxivV1.SupplementalHMixedCoareaCoordinates
import RectangleCLTArxivV1.SupplementalHWeightedThresholdDerivative
import RectangleCLTArxivV1.SupplementalHRidgeGreen
import RectangleCLTArxivV1.SupplementalHResidualGreen

/-! Continuity of the actual signed ridge value at ordinary residual
triple slack. No derivative of a pair section, quadruple regularity, or
full-family independence is assumed. Nonsimple rank-three collisions
are allowed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

/-- A pair score splits into one fixed integrable residual quadratic
weight and the varying normal squared length times the actual hard
event probability. -/
theorem hardGaussianPairSignedSection_eq_fixed_residual {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (he : vectorNormSq e=1) (hf : vectorNormSq f=1)
    (hef : faceDot e f=0) (a c : ℝ) :
    hardGaussianPairSignedSection s u b e f a c=
      (∫ g,(gaussianFiniteThresholdEvent s (hardPairResidualNormals u e f)
        (hardPairResidualLevels u b e f a c)).indicator
          (fun g => vectorNormSq g-faceDot e g^2-faceDot f g^2-(r:ℝ)) g
          ∂standardGaussian r)+
      (a^2+c^2)*gaussianFiniteThresholdCDF s (hardPairResidualNormals u e f)
        (hardPairResidualLevels u b e f a c) := by
  let v := hardPairResidualNormals u e f
  let d := hardPairResidualLevels u b e f a c
  let F := fun g => vectorNormSq g-faceDot e g^2-faceDot f g^2-(r:ℝ)
  have hFi : Integrable F (standardGaussian r) :=
    ((((standardGaussian_integrable_vectorNormSq _).sub
      (standardGaussian_integrable_faceDot_sq e)).sub
      (standardGaussian_integrable_faceDot_sq f)).sub (integrable_const _))
  rw [gaussianFiniteThresholdCDF_eq_integral,← integral_const_mul,
    ← integral_add (hFi.indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _))
      (((integrable_const (1:ℝ)).indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _)).const_mul _)]
  unfold hardGaussianPairSignedSection
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    have hiff := gaussianPairSectionPoint_mem_event_iff s u b e f a c g hef
    by_cases hg : g∈gaussianFiniteThresholdEvent s v d
    · rw [indicator_of_mem (hiff.mpr hg),indicator_of_mem hg,indicator_of_mem hg]
      dsimp only [F]
      rw [vectorNormSq_gaussianPairSectionPoint e f he hf hef]
      ring
    · rw [indicator_of_not_mem (fun h => hg (hiff.mp h)),indicator_of_not_mem hg,
        indicator_of_not_mem hg,mul_zero,add_zero])

/-- Joint threshold and normal-level continuity of a fixed pair section,
requiring only that its retained zero residual inequalities have nonzero
slack at the point in question. -/
theorem continuousAt_hardGaussianPairSignedSection_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (he : vectorNormSq e=1) (hf : vectorNormSq f=1)
    (hef : faceDot e f=0) (A C : Vector m → ℝ)
    (hA : ContinuousAt A b) (hC : ContinuousAt C b)
    (hreg : ∀ k∈s,hardPairResidualNormal e f (u k)≠0 ∨
      b k-A b*faceDot (u k) e-C b*faceDot (u k) f≠0) :
    ContinuousAt (fun d => hardGaussianPairSignedSection s u d e f (A d) (C d)) b := by
  let v := hardPairResidualNormals u e f
  let D := fun d => hardPairResidualLevels u d e f (A d) (C d)
  let F := fun g => vectorNormSq g-faceDot e g^2-faceDot f g^2-(r:ℝ)
  have hFm : Measurable F := by
    have hnorm : Measurable (fun g : Vector r => vectorNormSq g) := by
      unfold vectorNormSq
      fun_prop
    exact (((hnorm.sub ((continuous_faceDot_left e).measurable.pow_const 2)).sub
      ((continuous_faceDot_left f).measurable.pow_const 2)).sub_const _)
  have hFi : Integrable F (standardGaussian r) :=
    ((((standardGaussian_integrable_vectorNormSq _).sub
      (standardGaussian_integrable_faceDot_sq e)).sub
      (standardGaussian_integrable_faceDot_sq f)).sub (integrable_const _))
  have hD : ContinuousAt D b := by
    apply continuousAt_pi.mpr
    intro k
    exact (((continuous_apply k).continuousAt.sub
      (hA.mul_const _)).sub (hC.mul_const _))
  have hweighted := (continuousAt_weighted_gaussianFiniteThreshold_of_slack s v (D b)
    hreg F hFm hFi).comp hD
  have hprob := (continuousAt_gaussianFiniteThresholdCDF_of_slack s v (D b) hreg).comp hD
  have hc := hweighted.add (((hA.pow 2).add (hC.pow 2)).mul hprob)
  convert hc using 1
  funext d
  exact hardGaussianPairSignedSection_eq_fixed_residual s u d e f he hf hef (A d) (C d)

/-- Ordinary first-facet residual regularity already supplies all the
boundary slack needed for continuity of the actual pair value. It does
not require local regularity of the double-residual event itself. -/
theorem residualThresholdRegularity_conditional_pair_value_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hreg : ResidualThresholdRegularity u b j)
    (hu : vectorNormSq (u j)=1) :
    ∀ k∈(Finset.univ.erase j).erase l,
      hardPairResidualNormal (u j) (gaussianPairConditionalDirection u j l) (u k)≠0 ∨
      b k-b j*faceDot (u k) (u j)-
        gaussianPairConditionalLevel u b j l*faceDot (u k) (gaussianPairConditionalDirection u j l)≠0 := by
  let q := gaussianPairConditionalDirection u j l
  have horth : faceDot (u j) q=0 := by
    dsimp only [q]
    rw [gaussianPairConditionalDirection,threshold_faceDot_smul_right,
      gaussianNormalProjection_orthogonal (u j) (u l) hu,mul_zero]
  have hl : l∈Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjl,Finset.mem_univ _⟩
  intro k hk
  have hr := (hreg l hl).2 k hk
  change gaussianNormalProjection q (gaussianNormalProjection (u j) (u k))≠0 ∨
    (b k-b j*faceDot (u k) (u j))-
      gaussianPairConditionalLevel u b j l*
        faceDot (gaussianNormalProjection (u j) (u k)) q≠0 at hr
  have hdot : faceDot (gaussianNormalProjection (u j) (u k)) q=faceDot (u k) q := by
    rw [gaussianNormalProjection,threshold_faceDot_sub_left,threshold_faceDot_smul_left,
      horth,mul_zero,sub_zero]
  rwa [hdot] at hr

theorem continuousAt_hardGaussianConditionalPairSignedSection_of_residual_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : ResidualThresholdRegularity u b j) :
    ContinuousAt (fun d => hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u d
      (u j) (gaussianPairConditionalDirection u j l) (d j)
      (gaussianPairConditionalLevel u d j l)) b := by
  have hg := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  apply continuousAt_hardGaussianPairSignedSection_of_slack _ u b _ _ hu hg.1 hg.2.1
    (fun d => d j) (fun d => gaussianPairConditionalLevel u d j l)
    (continuous_apply j).continuousAt (by unfold gaussianPairConditionalLevel; fun_prop)
  exact residualThresholdRegularity_conditional_pair_value_slack u b j l hjl hreg hu

theorem continuousAt_hardGaussianSignedRidgeTerm_of_residual_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hreg : ResidualThresholdRegularity u b j) :
    ContinuousAt (fun d => hardGaussianSignedRidgeTerm u d j l) b := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hjl : j≠l := by
      intro h
      subst l
      exact hp.2 (sub_self _)
    have hsec := continuousAt_hardGaussianConditionalPairSignedSection_of_residual_slack
      u b j l hjl hu hv hp.1 hp.2 hreg
    have hnative : ContinuousAt (fun d =>
      hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u d
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u d j l) (thresholdPairSecondLevel u d j l)) b := by
      convert hsec using 1
      funext d
      exact (hardGaussianConditionalPairSignedSection_eq_pairSection _ u d j l hu hv hp.1 hp.2).symm
    have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
      (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
    have hw : Continuous (fun d => hardGaussianRidgeNormalWeight u d j l) := by
      unfold hardGaussianRidgeNormalWeight
      have ha : Continuous (fun d : Vector m => thresholdPairFirstLevel u d j l) := by
        unfold thresholdPairFirstLevel
        fun_prop
      have hc : Continuous (fun d : Vector m => thresholdPairSecondLevel u d j l) := by
        unfold thresholdPairSecondLevel
        fun_prop
      exact (continuous_const.mul (hpdf.comp ha)).mul (hpdf.comp hc)
    simpa only [hardGaussianSignedRidgeTerm,hp,if_true] using hw.continuousAt.mul hnative
  · simpa only [hardGaussianSignedRidgeTerm,hp,if_false] using
      (continuousAt_const : ContinuousAt (fun _ : Vector m => (0:ℝ)) b)

/-- The actual native signed ridge quantity is continuous under only
ordinary residual triple slack. Nonsimple rank-three intersections and
dependent families are allowed. -/
theorem continuousAt_hardGaussianWeightedRidgeIntegral_of_residual_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : ∀ j,ResidualThresholdRegularity u b j) :
    ContinuousAt (hardGaussianWeightedRidgeIntegral u) b := by
  unfold hardGaussianWeightedRidgeIntegral
  exact tendsto_const_nhds.mul (tendsto_finset_sum _ (fun q _ =>
    continuousAt_hardGaussianSignedRidgeTerm_of_residual_slack u b q.1 q.2
      (hu _) (hu _) (hreg _)))

end
end RectangleCLTArxivV1

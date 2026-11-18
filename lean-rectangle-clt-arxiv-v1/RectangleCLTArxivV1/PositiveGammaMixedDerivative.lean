import RectangleCLTArxivV1.PositiveMixedCoareaBounds
import RectangleCLTArxivV1.PositiveMixedCoareaDerivative
import RectangleCLTArxivV1.SupplementalHGammaLocalDerivative
import RectangleCLTArxivV1.SupplementalHRidgeMeasurable

/-! Actual positive mixed Gamma coarea derivatives for mass and the
original pair-plane quadratic test. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology NNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def positiveGammaMixedMassKernel {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
    gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2))*
      hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)

def positiveGammaMixedPlaneKernel {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  positiveGammaMixedMassKernel u b j l*((b j)^2+(gaussianPairConditionalLevel u b j l)^2)

theorem measurable_positiveGammaMixedMassKernel {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    Measurable (fun b => positiveGammaMixedMassKernel u b j l) := by
  unfold positiveGammaMixedMassKernel
  apply Measurable.mul
  · apply Measurable.div_const
    exact ((measurable_gaussianPDFReal 0 1).comp (by unfold thresholdPairFirstLevel; fun_prop)).mul
      ((measurable_gaussianPDFReal 0 1).comp (by unfold thresholdPairSecondLevel; fun_prop))
  · exact measurable_hardPairSection_integral_threshold _ u _ _ _ _
      (by unfold thresholdPairFirstLevel; fun_prop)
      (by unfold thresholdPairSecondLevel; fun_prop) _ measurable_const

theorem measurable_positiveGammaMixedPlaneKernel {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    Measurable (fun b => positiveGammaMixedPlaneKernel u b j l) := by
  unfold positiveGammaMixedPlaneKernel
  exact (measurable_positiveGammaMixedMassKernel u j l).mul
    (((measurable_pi_apply j).pow_const 2).add
      ((by unfold gaussianPairConditionalLevel; fun_prop : Measurable (fun b : Vector m => gaussianPairConditionalLevel u b j l)).pow_const 2))

theorem hasDerivAt_gamma_positiveMass_offset {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m) (hjl : j≠l)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (q : ℕ) :
    HasDerivAt (fun t => ∫ e, positiveMixedFirstMassDensity u
      (fun k => (gammaAdjustedThreshold (Function.update a l (a l+t)) h e k-faceDot (u k) x)/σ) j
      ∂gammaRectangleLaw m q)
      (σ⁻¹*(∫ e, positiveGammaMixedMassKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l
        ∂gammaRectangleLaw m q)) 0 := by
  have hd : ∀ᵐ b : Vector m ∂volume,
      HasDerivAt (fun z => positiveMixedFirstMassDensity u (Function.update b l z) j)
        (positiveGammaMixedMassKernel u b j l) (b l) := by
    filter_upwards [ae_residualThresholdRegularity u] with b hb
    exact hasDerivAt_positiveMixedFirstMassDensity_native u b j l hjl (hu j) (hu l) hp hm
      ((hb j).mixedGaussianSectionSlack hjl.symm)
  exact supplementalH_hasDerivAt_gamma_threshold_average u a hh hσ x l q
    (fun b => positiveMixedFirstMassDensity u b j) (fun b => positiveGammaMixedMassKernel u b j l)
    (measurable_positiveMixedFirstMassDensity u j) (measurable_positiveGammaMixedMassKernel u j l)
    positiveMixedGaussianPeak (fun b => positiveMixedFirstMassDensity_norm_le u b j)
    ⟨positiveMixedMassBudget/gaussianThresholdResidualScale u j l,
      div_nonneg positiveMixedMassBudget_nonneg (by unfold gaussianThresholdResidualScale; positivity)⟩
    (fun b => lipschitzWith_positiveMixedFirstMassDensity_update u b j l hjl (hu j) (hu l) hp hm) hd

theorem hasDerivAt_gamma_positivePlane_offset {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m) (hjl : j≠l)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (q : ℕ) :
    HasDerivAt (fun t => ∫ e, positiveMixedFirstPlaneDensity u
      (fun k => (gammaAdjustedThreshold (Function.update a l (a l+t)) h e k-faceDot (u k) x)/σ) j l
      ∂gammaRectangleLaw m q)
      (σ⁻¹*(∫ e, positiveGammaMixedPlaneKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l
        ∂gammaRectangleLaw m q)) 0 := by
  have hd : ∀ᵐ b : Vector m ∂volume,
      HasDerivAt (fun z => positiveMixedFirstPlaneDensity u (Function.update b l z) j l)
        (positiveGammaMixedPlaneKernel u b j l) (b l) := by
    filter_upwards [ae_residualThresholdRegularity u] with b hb
    exact hasDerivAt_positiveMixedFirstPlaneDensity_native u b j l hjl (hu j) (hu l) hp hm
      ((hb j).mixedGaussianSectionSlack hjl.symm)
  exact supplementalH_hasDerivAt_gamma_threshold_average u a hh hσ x l q
    (fun b => positiveMixedFirstPlaneDensity u b j l) (fun b => positiveGammaMixedPlaneKernel u b j l)
    (measurable_positiveMixedFirstPlaneDensity u j l) (measurable_positiveGammaMixedPlaneKernel u j l)
    (3*positiveMixedGaussianPeak) (fun b => positiveMixedFirstPlaneDensity_norm_le u b j l (hu j) (hu l) hp hm)
    ⟨positiveMixedPlaneBudget/gaussianThresholdResidualScale u j l,
      div_nonneg positiveMixedPlaneBudget_nonneg (by unfold gaussianThresholdResidualScale; positivity)⟩
    (fun b => lipschitzWith_positiveMixedFirstPlaneDensity_update u b j l hjl (hu j) (hu l) hp hm) hd

end
end RectangleCLTArxivV1

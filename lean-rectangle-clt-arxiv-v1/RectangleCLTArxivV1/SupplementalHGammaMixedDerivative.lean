import RectangleCLTArxivV1.SupplementalHGammaLocalDerivative
import RectangleCLTArxivV1.SupplementalHGammaSignedFace
import RectangleCLTArxivV1.SupplementalHMixedCoareaLipschitz
import RectangleCLTArxivV1.SupplementalHRidgeMeasurable

/-! Actual signed two-normal coarea kernels under the Gamma law. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology NNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def supplementalHSignedMixedKernel {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
    gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/Real.sqrt (1-faceDot (u j) (u l)^2))*
      hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)

theorem measurable_supplementalHSignedMixedKernel {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    Measurable (fun b => supplementalHSignedMixedKernel u b j l) := by
  unfold supplementalHSignedMixedKernel
  apply Measurable.mul
  · apply Measurable.div_const
    exact ((measurable_gaussianPDFReal 0 1).comp (by unfold thresholdPairFirstLevel; fun_prop)).mul
      ((measurable_gaussianPDFReal 0 1).comp (by unfold thresholdPairSecondLevel; fun_prop))
  · apply measurable_hardPairSection_integral_threshold _ u _ _ _ _
      (by unfold thresholdPairFirstLevel; fun_prop)
      (by unfold thresholdPairSecondLevel; fun_prop) _
      (by unfold vectorNormSq; fun_prop)

theorem supplementalH_hasDerivAt_gamma_signedMixed_offset {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m) (hjl : j≠l)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (q : ℕ) :
    HasDerivAt (fun t => ∫ e,
      gaussianPDFReal 0 1 ((gammaAdjustedThreshold (Function.update a l (a l+t)) h e j-faceDot (u j) x)/σ)*
        Printed.thresholdSignedSection u
          (fun k => (gammaAdjustedThreshold (Function.update a l (a l+t)) h e k-faceDot (u k) x)/σ) j
          ((gammaAdjustedThreshold (Function.update a l (a l+t)) h e j-faceDot (u j) x)/σ)
      ∂gammaRectangleLaw m q)
      (σ⁻¹*(∫ e, supplementalHSignedMixedKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l
        ∂gammaRectangleLaw m q)) 0 := by
  let ψ := fun b : Vector m => gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u b j (b j)
  have hψ : Measurable ψ := ((measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply j)).mul
    (measurable_thresholdSignedSection_threshold u j)
  have hA (b) : ‖ψ b‖≤gaussianSignedFaceDensityBudget (n+1) :=
    norm_gaussianSignedFace_section_density_le u b j (hu j) (b j)
  let B : ℝ≥0 := ⟨gaussianMixedSectionDensityBudget (n+1)/gaussianThresholdResidualScale u j l,
    div_nonneg (gaussianMixedSectionDensityBudget_nonneg _)
      (by unfold gaussianThresholdResidualScale; positivity)⟩
  have hLip (b) : LipschitzWith B (fun z => ψ (Function.update b l z)) := by
    simpa only [ψ,Function.update_of_ne hjl] using
      lipschitzWith_gaussianSignedFacetDensity_update u b j l hjl (hu j) (hu l) hp hm
  have hd : ∀ᵐ b : Vector m ∂volume,
      HasDerivAt (fun z => ψ (Function.update b l z)) (supplementalHSignedMixedKernel u b j l) (b l) := by
    filter_upwards [ae_hasDerivAt_gaussianSignedFacetDensity_update u hu] with b hb
    simpa only [ψ,Function.update_of_ne hjl,supplementalHSignedMixedKernel] using hb j l hjl hp hm
  exact supplementalH_hasDerivAt_gamma_threshold_average u a hh hσ x l q ψ
    (fun b => supplementalHSignedMixedKernel u b j l) hψ (measurable_supplementalHSignedMixedKernel u j l)
    (gaussianSignedFaceDensityBudget (n+1)) hA B hLip hd

end
end RectangleCLTArxivV1

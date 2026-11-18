import RectangleCLTArxivV1.PositiveFirstCoareaBounds
import RectangleCLTArxivV1.PositiveFirstCoareaDerivative
import RectangleCLTArxivV1.SupplementalHGammaLocalDerivative

/-! Genuine first Gamma coarea for positive mass and actual pair-plane
quadratic tests. Every hard derivative and global domination premise is
discharged by the checked positive Gaussian slice proofs. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology NNReal
noncomputable section
set_option maxHeartbeats 1000000

theorem weighted_first_soft_coarea_of_hard_derivative {m n : ℕ}
    (u : Fin m → Vector (n+1)) (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j : Fin m) (q : ℕ) (P : Vector (n+1) → ℝ)
    (hPm : Measurable P) (hPi : Integrable P (standardGaussian (n+1)))
    (η : Vector m → ℝ) (hη : Measurable η) (B : ℝ≥0)
    (hLip : ∀ b,LipschitzWith B (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z) P))
    (hdiff : ∀ᵐ b : Vector m ∂volume,
      HasDerivAt (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z) P) (η b) (b j)) :
    (((q:ℝ)+1)/h)*(∫ g,P g*(logisticNullWeight u a h (x+σ • g)^(q+1)*
      logisticFaceWeight u a h (x+σ • g) j) ∂standardGaussian (n+1))=
      σ⁻¹*(∫ e,η (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) ∂gammaRectangleLaw m q) := by
  let ψ := fun b => gaussianFiniteWeightedThreshold Finset.univ u b P
  let S := fun t : ℝ => ∫ g,P g*logisticNullWeight u
    (Function.update a j (a j+t)) h (x+σ • g)^(q+1) ∂standardGaussian (n+1)
  have hψ := measurable_gaussianFiniteWeightedThreshold Finset.univ u P hPm
  have hA (b : Vector m) : ‖ψ b‖≤∫ g,|P g| ∂standardGaussian (n+1) := by
    simpa only [Real.norm_eq_abs] using abs_gaussianFiniteWeightedThreshold_le Finset.univ u b P hPi
  have hΓ := supplementalH_hasDerivAt_gamma_threshold_average u a hh hσ x j q ψ η hψ hη
    (∫ g,|P g| ∂standardGaussian (n+1)) hA B hLip hdiff
  have hd := supplementalH_hasDerivAt_integral_logistic_power_offset
    (standardGaussian (n+1)) (fun g => x+σ • g) (by fun_prop) P hPi u a hh j q (a j)
  have ht : HasDerivAt (fun t : ℝ => a j+t) 1 0 := by simpa using (hasDerivAt_id 0).const_add (a j)
  have hs := hd.comp_of_eq (0:ℝ) ht (by simp)
  have heS : S=(fun t => ∫ e,ψ
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ)
      ∂gammaRectangleLaw m q) := by
    funext t
    exact weighted_logistic_power_eq_gamma_weighted_threshold u (Function.update a j (a j+t)) hh hσ x q P hPi
  change HasDerivAt S _ 0 at hs
  rw [heS] at hs
  have he := hs.unique hΓ
  simpa only [add_zero,Function.update_eq_self,mul_one] using he

theorem positiveMass_soft_first_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j : Fin m) (q : ℕ) :
    (((q:ℝ)+1)/h)*(∫ g,logisticNullWeight u a h (x+σ • g)^(q+1)*
      logisticFaceWeight u a h (x+σ • g) j ∂standardGaussian (n+1))=
      σ⁻¹*(∫ e,positiveMixedFirstMassDensity u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j ∂gammaRectangleLaw m q) := by
  have hh' := weighted_first_soft_coarea_of_hard_derivative u a hh hσ x j q (fun _ => 1)
    measurable_const (integrable_const _) (fun b => positiveMixedFirstMassDensity u b j)
    (measurable_positiveMixedFirstMassDensity u j)
    ⟨positiveMixedGaussianPeak,positiveMixedGaussianPeak_nonneg⟩
    (fun b => lipschitzWith_positiveMassThreshold_update u b j (hu j))
    (ae_hasDerivAt_positiveMassThreshold_update u hu j)
  simpa only [one_mul] using hh'

theorem positivePlane_soft_first_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (q : ℕ) :
    (((q:ℝ)+1)/h)*(∫ g,positiveGaussianPlaneTest (u j) (gaussianPairConditionalDirection u j l) g*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*logisticFaceWeight u a h (x+σ • g) j)
        ∂standardGaussian (n+1))=
      σ⁻¹*(∫ e,positiveMixedFirstPlaneDensity u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l ∂gammaRectangleLaw m q) := by
  have hg := gaussianPairConditionalDirection_geometry_nonparallel u j l (hu j) (hu l) hp hm
  exact weighted_first_soft_coarea_of_hard_derivative u a hh hσ x j q _
    (measurable_positiveGaussianPlaneTest _ _) (integrable_positiveGaussianPlaneTest _ _)
    (fun b => positiveMixedFirstPlaneDensity u b j l) (measurable_positiveMixedFirstPlaneDensity u j l)
    ⟨3*positiveMixedGaussianPeak,mul_nonneg (by norm_num) positiveMixedGaussianPeak_nonneg⟩
    (fun b => lipschitzWith_positivePlaneThreshold_update u b j _ (hu j) hg.1 hg.2.1)
    (ae_hasDerivAt_positivePlaneThreshold_update u hu j l hp hm)

end
end RectangleCLTArxivV1

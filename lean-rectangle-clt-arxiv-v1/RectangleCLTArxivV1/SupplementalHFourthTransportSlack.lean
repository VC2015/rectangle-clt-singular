import RectangleCLTArxivV1.SupplementalHFourthTransportRidge

/-! Inactive hard ridge inequalities can be made strict under actual
local residual slack, without independence of the full face family. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem gaussianPairBase_ae_no_boundary_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : ResidualThresholdRegularity u b j) :
    ∀ᵐ g ∂standardGaussian r, ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)≠b k := by
  classical
  let s := (Finset.univ.erase j).erase l
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  let q := gaussianPairConditionalDirection u j l
  let c := gaussianPairConditionalLevel u b j l
  have hl : l∈Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjl,Finset.mem_univ _⟩
  have hlocal : ∀ k∈s,gaussianNormalProjection q (v k)≠0 ∨ d k-c*faceDot (v k) q≠0 :=
    (hreg l hl).2
  have hn := gaussianFiniteThreshold_ae_no_boundary_of_slack s
    (fun k => gaussianNormalProjection q (v k)) (fun k => d k-c*faceDot (v k) q) hlocal
  filter_upwards [hn] with g hg
  intro k hkj hkl he
  have hk := hg k (Finset.mem_erase.mpr ⟨hkl,Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ _⟩⟩)
  apply hk
  rw [← gaussianPairConditionalBase_eq_pairBase u b j l hu hv hp hm g] at he
  change faceDot (u k) (gaussianSectionPoint (u j) (b j) (gaussianSectionPoint q c g))=b k at he
  rw [gaussianSectionPoint_faceDot,gaussianSectionPoint_faceDot] at he
  change faceDot (gaussianNormalProjection q (gaussianNormalProjection (u j) (u k))) g=
    (b k-b j*faceDot (u k) (u j))-c*faceDot (gaussianNormalProjection (u j) (u k)) q
  linarith

theorem gaussianPairBase_probability_le_eq_lt_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : ResidualThresholdRegularity u b j) :
    (standardGaussian r).real {g | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)≤b k}=
      (standardGaussian r).real {g | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)<b k} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [gaussianPairBase_ae_no_boundary_of_slack u b j l hjl hu hv hp hm hreg] with g hg
  apply propext
  constructor
  · intro h k hkj hkl
    exact lt_of_le_of_ne (h k hkj hkl) (hg k hkj hkl)
  · intro h k hkj hkl
    exact (h k hkj hkl).le

/-- Closed residual density is exactly the strict true Gaussian pair
mass, with its genuine Gram Jacobian and the complete inactive family. -/
theorem hardGaussianRidgeDensity_eq_strict_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : ResidualThresholdRegularity u b j) :
    hardGaussianRidgeDensity u b j l=
      (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/
        Real.sqrt (1-faceDot (u j) (u l)^2))*
      (standardGaussian r).real {g | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)<b k} := by
  unfold hardGaussianRidgeDensity
  rw [gaussianPairBase_probability_le_eq_lt_of_slack u b j l hjl hu hv hp hm hreg]


/-- The Gram Jacobian cancels against the actual paired Green coefficient
before any absolute estimate. No inverse angular gap remains. -/
theorem hard_ridge_density_coefficient_le_fourth_event {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (hbound : ∀ z,‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R (gaussianPairBase u b j l z))
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian (n+1))) :
    |supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u j))
      (projectionEuclideanVector (u l)) (fourthRidgeNormalPoint u b j l)| *
        Real.sqrt (1-faceDot (u j) (u l)^2)*hardGaussianRidgeDensity u b j l≤
      (8192*Real.exp ((3:ℝ)/2))*(∫ g,(fourthPairEvent u b R j l).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := by
  have hσ : 0<gaussianThresholdResidualScale u j l := by
    rw [thresholdPair_residualScale_eq u j l hu hv hp hm]
    exact mul_pos (mul_pos (by norm_num) (div_pos (norm_pos_iff.mpr hp) (by norm_num)))
      (div_pos (norm_pos_iff.mpr hm) (by norm_num))
  rw [gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv] at hσ
  have he : |supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u j))
      (projectionEuclideanVector (u l)) (fourthRidgeNormalPoint u b j l)| *
        Real.sqrt (1-faceDot (u j) (u l)^2)*hardGaussianRidgeDensity u b j l=
      (|supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u j))
        (projectionEuclideanVector (u l)) (fourthRidgeNormalPoint u b j l)| *
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l))*
        (standardGaussian (n+1)).real {z | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l z)<b k} := by
    rw [hardGaussianRidgeDensity_eq_strict_of_slack u b j l hjl hu hv hp hm hreg]
    field_simp [hσ.ne']
    ring
  rw [he]
  exact hard_ridge_coefficient_le_fourth_event_strict u b j l hu hv hp hm R hRm hR hRadd hbound hR4

end
end RectangleCLTArxivV1

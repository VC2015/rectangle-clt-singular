import RectangleCLTArxivV1.SupplementalHFourthTransportGeometry
import RectangleCLTArxivV1.SupplementalHFourthTransportFacet
import RectangleCLTArxivV1.SupplementalHFourthTransportSlack

/-! The actual finite sum of weighted facet/ridge coefficients is paid
by one common outward fourth-radius Gaussian expectation. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def fourthGreenTubeCoefficient {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (q : Fin m × Fin m) : ℝ := by
  classical
  exact if q.1=q.2 then abs (|b q.1| *(b q.1^2-1))*gaussianThresholdFirst u b q.1 else
    if projectionEuclideanVector (u q.1)+projectionEuclideanVector (u q.2)≠0 ∧
        projectionEuclideanVector (u q.1)-projectionEuclideanVector (u q.2)≠0 then
      |supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u q.1))
        (projectionEuclideanVector (u q.2)) (fourthRidgeNormalPoint u b q.1 q.2)| *
        Real.sqrt (1-faceDot (u q.1) (u q.2)^2)*hardGaussianRidgeDensity u b q.1 q.2 else 0

/-- This finite sum uses the genuine Gaussian surface coefficients. Local
residual slack handles dependent faces and all parallel terms are removed
only where their actual Green coefficient vanishes. -/
theorem fourthGreenTubeCoefficient_sum_le {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : ∀ j,ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (hface : ∀ j x,|faceDot (u j) x|≤fourthTransportRadius R x)
    (hpair : ∀ j l,projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 →
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 →
      ∀ z,‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R (gaussianPairBase u b j l z))
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian (n+1))) :
    (∑ q : Fin m × Fin m,fourthGreenTubeCoefficient u b q)≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,(fourthOuterLayer u b R).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := by
  classical
  let C := 8192*Real.exp ((3:ℝ)/2)
  have hC : 0≤C := by dsimp [C]; positivity
  have he (q : Fin m × Fin m) : fourthGreenTubeCoefficient u b q≤
      C*(∫ g,(fourthStratumEvent u b R q).indicator (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := by
    unfold fourthGreenTubeCoefficient fourthStratumEvent
    split_ifs with hq hpairq
    · have hb := hard_facet_coefficient_le_fourth_event u b q.1 (hu q.1) (hreg q.1)
        R hRm hR hRadd (hface q.1) hR4
      apply hb.trans
      apply mul_le_mul_of_nonneg_right
      · dsimp [C]
        nlinarith [Real.exp_pos ((3:ℝ)/2)]
      · exact integral_nonneg (fun _ => indicator_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (hR _)) 4) _)
    · exact hard_ridge_density_coefficient_le_fourth_event u b q.1 q.2 hq (hu q.1) (hu q.2)
        hpairq.1 hpairq.2 (hreg q.1) R hRm hR hRadd (hpair _ _ hpairq.1 hpairq.2) hR4
    · simp
  calc
    _ ≤ ∑ q : Fin m × Fin m,C*(∫ g,(fourthStratumEvent u b R q).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := Finset.sum_le_sum (fun q _ => he q)
    _ = C*(∑ q : Fin m × Fin m,∫ g,(fourthStratumEvent u b R q).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*(2*(∫ g,(fourthOuterLayer u b R).indicator (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1))) :=
      mul_le_mul_of_nonneg_left (fourthStratumEvent_integral_sum_le u b R hRm hR hRadd hu hR4) hC
    _ = _ := by dsimp [C]; ring

end
end RectangleCLTArxivV1

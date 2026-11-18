import RectangleCLTArxivV1.SupplementalHPositiveEdgeTransport
import RectangleCLTArxivV1.SupplementalHFourthTransportThreeFace

/-! The actual positive edge mass and projected second moment use separate
Gaussian radius powers. Ordered pairs are paid at most twice. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def positiveEdgeTubeCoefficient {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (k : ℕ) (q : Fin m × Fin m) : ℝ := by
  classical
  exact if q.1=q.2 then 0 else
    if projectionEuclideanVector (u q.1)+projectionEuclideanVector (u q.2)≠0 ∧
        projectionEuclideanVector (u q.1)-projectionEuclideanVector (u q.2)≠0 then
      (Real.arccos ⟪projectionEuclideanVector (u q.1),projectionEuclideanVector (u q.2)⟫_ℝ*
        ‖fourthRidgeNormalPoint u b q.1 q.2‖^k)*
        Real.sqrt (1-faceDot (u q.1) (u q.2)^2)*hardGaussianRidgeDensity u b q.1 q.2
    else 0

theorem fourthStratumEvent_integral_sum_le_power {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ j,vectorNormSq (u j)=1)
    (k : ℕ) (hRk : Integrable (fun g => fourthTransportRadius R g^k) (standardGaussian r)) :
    (∑ q : Fin m × Fin m, ∫ g,(fourthStratumEvent u b R q).indicator
      (fun g => fourthTransportRadius R g^k) g ∂standardGaussian r)≤
      2*(∫ g,(fourthOuterLayer u b R).indicator (fun g => fourthTransportRadius R g^k) g ∂standardGaussian r) := by
  classical
  have hi q := hRk.indicator (measurableSet_fourthStratumEvent u b R hRm q)
  rw [← integral_finset_sum Finset.univ (fun q _ => hi q),← integral_const_mul]
  exact integral_mono (integrable_finset_sum _ (fun q _ => hi q))
    ((hRk.indicator (measurableSet_fourthOuterLayer u b R hRm)).const_mul 2)
    (fun g => fourthStratumEvent_indicator_sum_le u b R hR hRadd hu _
      (fun _ => pow_nonneg (zero_le_one.trans (hR _)) k) g)

theorem positiveEdgeTubeCoefficient_sum_of_fibers {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : ∀ j,ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (k d : ℕ) (C : ℝ) (hC : 0≤C)
    (hRd : Integrable (fun g => fourthTransportRadius R g^d) (standardGaussian (n+1)))
    (hfiber : ∀ j l,
      projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 →
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 → ∀ z,
      (Real.arccos ⟪projectionEuclideanVector (u j),projectionEuclideanVector (u l)⟫_ℝ*
        ‖fourthRidgeNormalPoint u b j l‖^k)*
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) ≤
        C*(∫ st in ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
          (1/(4*fourthTransportRadius R (gaussianPairBase u b j l z))),
          fourthTransportRadius R (gaussianPairBase u b j l z+st.1 • thresholdPairBisector u j l+
            st.2 • thresholdPairDifference u j l)^d*
          gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l+st.1)*
          gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l+st.2) ∂(volume : Measure ℝ).prod volume)) :
    (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b k q)≤
      (2*C)*(∫ g,(fourthOuterLayer u b R).indicator
        (fun g => fourthTransportRadius R g^d) g ∂standardGaussian (n+1)) := by
  classical
  have he (q : Fin m × Fin m) : positiveEdgeTubeCoefficient u b k q ≤
      C*(∫ g,(fourthStratumEvent u b R q).indicator
        (fun g => fourthTransportRadius R g^d) g ∂standardGaussian (n+1)) := by
    have hnonneg : 0≤C*(∫ g,(fourthStratumEvent u b R q).indicator
        (fun g => fourthTransportRadius R g^d) g ∂standardGaussian (n+1)) :=
      mul_nonneg hC (integral_nonneg (fun _ => indicator_nonneg
        (fun _ _ => pow_nonneg (zero_le_one.trans (hR _)) d) _))
    by_cases hq : q.1=q.2
    · simpa only [positiveEdgeTubeCoefficient,if_pos hq] using hnonneg
    · by_cases hpair : projectionEuclideanVector (u q.1)+projectionEuclideanVector (u q.2)≠0 ∧
          projectionEuclideanVector (u q.1)-projectionEuclideanVector (u q.2)≠0
      · simpa only [positiveEdgeTubeCoefficient,if_neg hq,if_pos hpair,fourthStratumEvent] using
          positiveRidge_coefficient_le_event u b q.1 q.2 (hu q.1) (hu q.2)
            hpair.1 hpair.2 hq (hreg q.1) R hRm hR d _ C hC hRd
            (hfiber q.1 q.2 hpair.1 hpair.2)
      · simpa only [positiveEdgeTubeCoefficient,if_neg hq,if_neg hpair] using hnonneg
  calc
    _ ≤ ∑ q : Fin m × Fin m,C*(∫ g,(fourthStratumEvent u b R q).indicator
        (fun g => fourthTransportRadius R g^d) g ∂standardGaussian (n+1)) :=
      Finset.sum_le_sum (fun q _ => he q)
    _ = C*(∑ q : Fin m × Fin m,∫ g,(fourthStratumEvent u b R q).indicator
        (fun g => fourthTransportRadius R g^d) g ∂standardGaussian (n+1)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C*(2*(∫ g,(fourthOuterLayer u b R).indicator
        (fun g => fourthTransportRadius R g^d) g ∂standardGaussian (n+1))) :=
      mul_le_mul_of_nonneg_left (fourthStratumEvent_integral_sum_le_power u b R hRm hR hRadd hu d hRd) hC
    _ = _ := by ring

theorem positiveEdgeTubeCoefficient_second_bound {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : ∀ j,ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (hbound : ∀ j l,projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 →
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 →
      ∀ z,‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R (gaussianPairBase u b j l z))
    (hR2 : Integrable (fun g => fourthTransportRadius R g^2) (standardGaussian (n+1))) :
    (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 0 q)≤
      (1024*Real.pi*Real.exp ((3:ℝ)/2))*(∫ g,(fourthOuterLayer u b R).indicator
        (fun g => fourthTransportRadius R g^2) g ∂standardGaussian (n+1)) := by
  have hb := positiveEdgeTubeCoefficient_sum_of_fibers u b hu hreg R hRm hR hRadd
    0 2 (512*Real.pi*Real.exp ((3:ℝ)/2)) (by positivity) hR2
    (by
      intro j l hp hm z
      simpa only [pow_zero,mul_one] using
        (positiveRidge_angle_second_fiber u b j l (hu j) (hu l) hp hm R hRm hR hRadd
          (gaussianPairBase u b j l z) (hbound j l hp hm z)))
  convert hb using 1 <;> ring

theorem positiveEdgeTubeCoefficient_fourth_bound {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : ∀ j,ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (hbound : ∀ j l,projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 →
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 →
      ∀ z,‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R (gaussianPairBase u b j l z))
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian (n+1))) :
    (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 2 q)≤
      (4096*Real.pi*Real.exp ((3:ℝ)/2))*(∫ g,(fourthOuterLayer u b R).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := by
  have hb := positiveEdgeTubeCoefficient_sum_of_fibers u b hu hreg R hRm hR hRadd
    2 4 (2048*Real.pi*Real.exp ((3:ℝ)/2)) (by positivity) hR4
    (fun j l hp hm z => positiveRidge_angle_normSq_fourth_fiber u b j l (hu j) (hu l) hp hm
      R hRm hR hRadd (gaussianPairBase u b j l z) (hbound j l hp hm z))
  convert hb using 1 <;> ring

theorem positiveEdgeTubeCoefficient_second_threeFace_bound {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ j,ResidualThresholdRegularity (fun k => U (f k)) b j) :
    (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun k => U (f k)) b 0 q)≤
      (1024*Real.pi*Real.exp ((3:ℝ)/2))*(∫ g,
        (fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
        (fun g => supplementalHRadius U g^2) g ∂standardGaussian (n+1)) := by
  exact positiveEdgeTubeCoefficient_second_bound (fun k => U (f k)) b hu hreg
    (fourthThreeFaceRadius U) (continuous_fourthThreeFaceRadius U) (fourthThreeFaceRadius_ge_one U)
    (fourthThreeFaceRadius_add_le U)
    (fun j l hplus hminus z => fourthRidgeNormalPoint_norm_le_threeFaceRadius hp U f b j l
      (hu j) (hu l) hplus hminus z)
    (supplementalHRadius_moment_le hp U 2).1

theorem positiveEdgeTubeCoefficient_fourth_threeFace_bound {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ j,ResidualThresholdRegularity (fun k => U (f k)) b j) :
    (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun k => U (f k)) b 2 q)≤
      (4096*Real.pi*Real.exp ((3:ℝ)/2))*(∫ g,
        (fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  exact positiveEdgeTubeCoefficient_fourth_bound (fun k => U (f k)) b hu hreg
    (fourthThreeFaceRadius U) (continuous_fourthThreeFaceRadius U) (fourthThreeFaceRadius_ge_one U)
    (fourthThreeFaceRadius_add_le U)
    (fun j l hplus hminus z => fourthRidgeNormalPoint_norm_le_threeFaceRadius hp U f b j l
      (hu j) (hu l) hplus hminus z)
    (supplementalHRadius_moment_le hp U 4).1

end
end RectangleCLTArxivV1

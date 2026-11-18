import RectangleCLTArxivV1.SupplementalHActualFacetAffine
import RectangleCLTArxivV1.SupplementalHActualFacetOuterLayer

/-! The pointwise actual facet surface estimate is paid by the ORIGINAL
polyhedron's outer layer, after one exact fixed facet selection. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actualFacet_fourthGreenCoefficient_single_le {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : ∀ j,ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (hface : ∀ j x,|faceDot (u j) x|≤fourthTransportRadius R x)
    (hpair : ∀ j l,projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 →
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 →
      ∀ z,‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R (gaussianPairBase u b j l z))
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian (n+1)))
    (a : Fin m × Fin m) :
    fourthGreenTubeCoefficient u b a≤(8192*Real.exp ((3:ℝ)/2))*(∫ g,
      (fourthStratumEvent u b R a).indicator (fun g => fourthTransportRadius R g^4) g
        ∂standardGaussian (n+1)) := by
  classical
  unfold fourthGreenTubeCoefficient fourthStratumEvent
  split_ifs with ha hpaira
  · have hb := hard_facet_coefficient_le_fourth_event u b a.1 (hu a.1) (hreg a.1)
      R hRm hR hRadd (hface a.1) hR4
    apply hb.trans
    apply mul_le_mul_of_nonneg_right
    · nlinarith [Real.exp_pos ((3:ℝ)/2)]
    · exact integral_nonneg (fun _ => indicator_nonneg
        (fun _ _ => pow_nonneg (zero_le_one.trans (hR _)) 4) _)
  · exact hard_ridge_density_coefficient_le_fourth_event u b a.1 a.2 ha (hu a.1) (hu a.2)
      hpaira.1 hpaira.2 (hreg a.1) R hRm hR hRadd (hpair _ _ hpaira.1 hpaira.2) hR4
  · simp

theorem actualFacet_selectedGreenCoefficient_sum_le_original_tube {p m q n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector (n+1),(∀ i,faceDot (U (f (e i))) y≤b (e i)) ↔
      ∀ k,faceDot (U (f k)) y≤b k)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hreg : ∀ j,ResidualThresholdRegularity (fun i => U (f (e i))) (fun i => b (e i)) j) :
    (∑ a : Fin q × Fin q,fourthGreenTubeCoefficient (fun i => U (f (e i))) (fun i => b (e i)) a)≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,
        (fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
          (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  let C := 8192*Real.exp ((3:ℝ)/2)
  have hC : 0≤C := by dsimp [C]; positivity
  have he (a : Fin q × Fin q) := actualFacet_fourthGreenCoefficient_single_le
    (fun i => U (f (e i))) (fun i => b (e i)) (fun i => hu (e i)) hreg
    (fourthThreeFaceRadius U) (continuous_fourthThreeFaceRadius U) (fourthThreeFaceRadius_ge_one U)
    (fourthThreeFaceRadius_add_le U)
    (fun i x => supplementalHRadius_face_abs_le hp U (f (e i)) (hu (e i)) x)
    (fun j l hplus hminus z => fourthRidgeNormalPoint_norm_le_threeFaceRadius hp U (fun i => f (e i))
      (fun i => b (e i)) j l (hu (e j)) (hu (e l)) hplus hminus z)
    (fourthThreeFaceRadius_fourth_integrable hp U) a
  calc
    _≤∑ a : Fin q × Fin q,C*(∫ g,
      (fourthStratumEvent (fun i => U (f (e i))) (fun i => b (e i)) (fourthThreeFaceRadius U) a).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) :=
      Finset.sum_le_sum (fun a _ => he a)
    _=C*(∑ a : Fin q × Fin q,∫ g,
      (fourthStratumEvent (fun i => U (f (e i))) (fun i => b (e i)) (fourthThreeFaceRadius U) a).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := (Finset.mul_sum _ _ _).symm
    _≤C*(2*(∫ g,(fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1))) :=
      mul_le_mul_of_nonneg_left
        (actualFacet_selectedEvent_integral_sum_le_original (fun k => U (f k)) b e hequiv hu
          (fourthThreeFaceRadius U) (continuous_fourthThreeFaceRadius U) (fourthThreeFaceRadius_ge_one U)
          (fourthThreeFaceRadius_add_le U) (fourthThreeFaceRadius_fourth_integrable hp U)) hC
    _=_ := by dsimp [C]; ring

/-- The selected actual facets are paid by the original complete
polyhedron's layer, without identifying the two expanded presentations. -/
theorem actualFacet_selected_weightedFacetIntegral_le_original_tube {p m q n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector (n+1),(∀ i,faceDot (U (f (e i))) y≤b (e i)) ↔
      ∀ k,faceDot (U (f k)) y≤b k)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hinterior : HasStrictFacetInterior (fun i => U (f (e i))) (fun i => b (e i)))
    (hwitness : HasIrredundantFacetWitnesses (fun i => U (f (e i))) (fun i => b (e i))) :
    |hardGaussianWeightedFacetIntegral (fun i => U (f (e i))) (fun i => b (e i))|≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,
        (fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
          (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  have hreg := actualFacet_residualThresholdRegularity _ _ hinterior hwitness
  exact (abs_hardGaussianWeightedFacetIntegral_le_coefficient_sum _ _ (fun i => hu (e i)) hreg).trans
    (actualFacet_selectedGreenCoefficient_sum_le_original_tube hp U f b e hequiv hu hreg)

theorem actualFacet_selected_weightedFacetIntegral_affine_le_original_tube {p m q n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector (n+1),(∀ i,faceDot (U (f (e i))) y≤a (e i)) ↔
      ∀ k,faceDot (U (f k)) y≤a k)
    (hu : ∀ k,vectorNormSq (U (f k))=1)
    (hinterior : HasStrictFacetInterior (fun i => U (f (e i))) (fun i => a (e i)))
    (hwitness : HasIrredundantFacetWitnesses (fun i => U (f (e i))) (fun i => a (e i)))
    (x : Vector (n+1)) {σ : ℝ} (hσ : 0<σ) :
    |hardGaussianWeightedFacetIntegral (fun i => U (f (e i)))
      (fun i => (a (e i)-faceDot (U (f (e i))) x)/σ)|≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,
        (gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U)).indicator
          (fun z => supplementalHRadius U z.2^4) (x,g) ∂standardGaussian (n+1)) := by
  have h := actualFacet_selected_weightedFacetIntegral_le_original_tube hp U f
    (fun k => (a k-faceDot (U (f k)) x)/σ) e
    (actualFacet_presentation_equivalence_affine (fun k => U (f k)) a e hequiv x hσ) hu
    (hinterior.affine x hσ) (hwitness.affine x hσ)
  apply h.trans_eq
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have he := fourthOuterLayer_shift_threshold (fun k => U (f k)) a x hσ (fourthThreeFaceRadius U) g
    change g∈fourthOuterLayer (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) (fourthThreeFaceRadius U) ↔
      (x,g)∈gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U) at he
    dsimp only
    by_cases hg : g∈fourthOuterLayer (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ) (fourthThreeFaceRadius U)
    · rw [indicator_of_mem hg,indicator_of_mem (he.mp hg)]
    · rw [indicator_of_not_mem hg,indicator_of_not_mem (fun h => hg (he.mpr h))])

end
end RectangleCLTArxivV1

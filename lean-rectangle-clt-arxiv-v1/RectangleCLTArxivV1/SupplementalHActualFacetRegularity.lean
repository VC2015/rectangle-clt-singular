import RectangleCLTArxivV1.SupplementalHActualFacetGeometry
import RectangleCLTArxivV1.SupplementalHFourthTransportFacetSum

/-! Genuine pointwise residual regularity and the actual weighted facet
surface estimate for a full-dimensional irredundant facet presentation. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actualFacet_pair_residual_slack {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b) (hwitness : HasIrredundantFacetWitnesses u b)
    (j k : Fin m) (hkj : k≠j) :
    gaussianNormalProjection (u j) (u k)≠0 ∨ b k-b j*faceDot (u k) (u j)≠0 := by
  by_cases hz : gaussianNormalProjection (u j) (u k)=0
  · right
    intro hb
    have hn : u k=faceDot (u k) (u j) • u j := sub_eq_zero.mp hz
    apply actualFacet_pair_affine_inconsistent u b hinterior hwitness j k hkj _ hn
    linarith
  · exact Or.inl hz

theorem actualFacet_triple_residual_slack {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b) (hwitness : HasIrredundantFacetWitnesses u b)
    (j k l : Fin m) (hjk : j≠k) (hlj : l≠j) (hlk : l≠k) :
    gaussianNormalProjection
      (localFiniteThresholdDirection (fun i => gaussianNormalProjection (u j) (u i)) k)
      (gaussianNormalProjection (u j) (u l))≠0 ∨
      (b l-b j*faceDot (u l) (u j))-
        ((b k-b j*faceDot (u k) (u j))/
          localFiniteThresholdScale (fun i => gaussianNormalProjection (u j) (u i)) k)*
          faceDot (gaussianNormalProjection (u j) (u l))
            (localFiniteThresholdDirection (fun i => gaussianNormalProjection (u j) (u i)) k)≠0 := by
  let V := fun i => gaussianNormalProjection (u j) (u i)
  let σ := localFiniteThresholdScale V k
  let D := localFiniteThresholdDirection V k
  let q := faceDot (V l) D
  let c := q*σ⁻¹
  change gaussianNormalProjection D (V l)≠0 ∨
    (b l-b j*faceDot (u l) (u j))-((b k-b j*faceDot (u k) (u j))/σ)*q≠0
  by_cases hz : gaussianNormalProjection D (V l)=0
  · right
    intro hb
    have hV : V l=c • V k := by
      have h := sub_eq_zero.mp hz
      change V l=q • (σ⁻¹ • V k) at h
      simpa only [smul_smul] using h
    let a := faceDot (u l) (u j)-c*faceDot (u k) (u j)
    have hn : u l=a • u j+c • u k := by
      calc
        u l=V l+faceDot (u l) (u j) • u j := by
          dsimp only [V,gaussianNormalProjection]
          module
        _=c • V k+faceDot (u l) (u j) • u j := by rw [hV]
        _=a • u j+c • u k := by
          dsimp only [V,gaussianNormalProjection,a]
          module
    apply actualFacet_triple_affine_inconsistent u b hinterior hwitness j k l hjk hlj hlk a c hn
    dsimp only [a,c]
    rw [div_eq_mul_inv] at hb
    linear_combination hb
  · exact Or.inl hz

/-- Actual irredundant facets discharge every pair and triple affine
slack needed by the signed facet Green identity, at this exact threshold. -/
theorem actualFacet_residualThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b) (hwitness : HasIrredundantFacetWitnesses u b) :
    ∀ j,ResidualThresholdRegularity u b j := by
  intro j k hk
  have hkj : k≠j := (Finset.mem_erase.mp hk).1
  refine ⟨actualFacet_pair_residual_slack u b hinterior hwitness j k hkj,?_⟩
  intro l hl
  have hlk : l≠k := (Finset.mem_erase.mp hl).1
  have hlj : l≠j := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
  exact actualFacet_triple_residual_slack u b hinterior hwitness j k l (Ne.symm hkj) hlj hlk

/-- Pointwise actual J_f bound for true irredundant facets with a strict
interior point. No affine-slack or desired surface bound is assumed. -/
theorem actualFacet_abs_weightedFacetIntegral_le_threeFace_tube {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hinterior : HasStrictFacetInterior (fun k => U (f k)) b)
    (hwitness : HasIrredundantFacetWitnesses (fun k => U (f k)) b) :
    |hardGaussianWeightedFacetIntegral (fun k => U (f k)) b|≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,
        (fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
          (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) :=
  abs_hardGaussianWeightedFacetIntegral_le_threeFace_tube hp U f b hu
    (actualFacet_residualThresholdRegularity _ b hinterior hwitness)

end
end RectangleCLTArxivV1

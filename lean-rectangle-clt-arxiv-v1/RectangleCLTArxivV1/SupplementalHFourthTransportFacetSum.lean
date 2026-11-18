import RectangleCLTArxivV1.SupplementalHFourthTransportThreeFace
import RectangleCLTArxivV1.SupplementalHFacetPairing

/-! The genuine signed weighted facet surface quantity is bounded by the
actual finite Green coefficients before Gaussian transport. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem fourthRidgeNormalPoint_supporting_levels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    ⟪projectionEuclideanVector (u j),fourthRidgeNormalPoint u b j l⟫_ℝ=b j ∧
      ⟪projectionEuclideanVector (u l),fourthRidgeNormalPoint u b j l⟫_ℝ=b l := by
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  have hef : faceDot e f=0 := thresholdPair_frame_orthogonal u j l hu hv
  have hs (v : Vector r) (t : ℝ) : gaussianSectionPoint v t 0=t • v := by
    ext k
    simp [gaussianSectionPoint,gaussianSectionResidual,faceDot]
  have hz : gaussianPairBase u b j l 0=a • e+c • f := by
    unfold gaussianPairBase gaussianPairSectionPoint
    rw [hs,gaussianSectionPoint_eq,threshold_faceDot_smul_right,hef,mul_zero,sub_zero]
    exact add_comm _ _
  have hpoint : projectionEuclideanVector (gaussianPairBase u b j l 0)=fourthRidgeNormalPoint u b j l := by
    rw [hz]
    rfl
  rw [← hpoint]
  constructor
  · exact (faceDot_eq_euclidean_inner (u j) (gaussianPairBase u b j l 0)).symm.trans
      (gaussianPairBase_left_level u b j l hu hv hp hm 0)
  · exact (faceDot_eq_euclidean_inner (u l) (gaussianPairBase u b j l 0)).symm.trans
      (gaussianPairBase_right_level u b j l hu hv hp hm 0)

theorem fourthRidgeNormalPoint_coefficient_identity {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    Real.sqrt (1-faceDot (u j) (u l)^2)*
      supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u j))
        (projectionEuclideanVector (u l)) (fourthRidgeNormalPoint u b j l)=
      |b j| *(b l-faceDot (u j) (u l)*b j)+|b l| *(b j-faceDot (u j) (u l)*b l) := by
  have hlev := fourthRidgeNormalPoint_supporting_levels u b j l hu hv hp hm
  have hσ : 0<gaussianThresholdResidualScale u j l := by
    rw [thresholdPair_residualScale_eq u j l hu hv hp hm]
    exact mul_pos (mul_pos (by norm_num) (div_pos (norm_pos_iff.mpr hp) (by norm_num)))
      (div_pos (norm_pos_iff.mpr hm) (by norm_num))
  rw [gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv] at hσ
  have hinner : ⟪projectionEuclideanVector (u j),projectionEuclideanVector (u l)⟫_ℝ=faceDot (u j) (u l) :=
    (faceDot_eq_euclidean_inner _ _).symm
  unfold supplementalHWeightedRidgeCoefficient supplementalHRidgeConormal
  simp only [inner_smul_left,inner_sub_left,conj_trivial,hlev.1,hlev.2]
  have hinner' : ⟪projectionEuclideanVector (u l),projectionEuclideanVector (u j)⟫_ℝ=faceDot (u j) (u l) := by
    rw [real_inner_comm]
    exact hinner
  simp only [hinner,hinner']
  field_simp [hσ.ne'] <;> ring

theorem fourthGreenTubeCoefficient_off_diagonal {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hreg : ResidualThresholdRegularity u b j) :
    fourthGreenTubeCoefficient u b (j,l)=
      abs ((|b j| *(b l-faceDot (u j) (u l)*b j)+
        |b l| *(b j-faceDot (u j) (u l)*b l))*hardFacetResidualDensity u b j l) := by
  classical
  unfold fourthGreenTubeCoefficient
  simp only [hjl,ite_false]
  split_ifs with hp
  · rw [← fourthRidgeNormalPoint_coefficient_identity u b j l hu hv hp.1 hp.2,
      hardFacetResidualDensity_eq_ridgeDensity u b j l hjl hu hv hp.1 hp.2 hreg,
      abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (hardGaussianRidgeDensity_nonneg _ _ _ _)]
    ring
  · have hpar : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)=0 ∨
        projectionEuclideanVector (u j)-projectionEuclideanVector (u l)=0 := by tauto
    have hz := gaussianNormalProjection_pair_zero_of_parallel_unit u j l hu hv hpar
    have hslack := (hreg l (Finset.mem_erase.mpr ⟨Ne.symm hjl,Finset.mem_univ _⟩)).1
    rw [hardFacetResidualDensity_zero_of_parallel_slack u b j l hjl hz.1
      (hslack.resolve_left (fun hn => hn hz.1)),mul_zero,abs_zero]

/-- Actual J_f: the two oriented conormal terms are paired before absolute
values, and genuinely parallel terms vanish by local affine slack. -/
theorem abs_hardGaussianWeightedFacetIntegral_le_coefficient_sum {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : ∀ j,ResidualThresholdRegularity u b j) :
    |hardGaussianWeightedFacetIntegral u b|≤∑ q : Fin m × Fin m,fourthGreenTubeCoefficient u b q := by
  classical
  let A := fun j => |b j| *(b j^2-1)*gaussianThresholdFirst u b j
  let B := fun j l => (|b j| *(b l-faceDot (u j) (u l)*b j)+
    |b l| *(b j-faceDot (u j) (u l)*b l))*hardFacetResidualDensity u b j l
  have hdiag (j : Fin m) : fourthGreenTubeCoefficient u b (j,j)=|A j| := by
    have hf : 0≤gaussianThresholdFirst u b j := by
      rw [gaussianThresholdFirst_eq_section_of_slack u b j (hu j)
        (fun l hl => (hreg j l (Finset.mem_erase.mpr ⟨hl,Finset.mem_univ _⟩)).1)]
      exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)
    simp only [fourthGreenTubeCoefficient,ite_true,A,abs_mul,abs_of_nonneg hf]
  have hsum : (∑ q : Fin m × Fin m,fourthGreenTubeCoefficient u b q)=
      (∑ j,|A j|)+(∑ j,∑ l∈Finset.univ.erase j,|B j l|) := by
    rw [Fintype.sum_prod_type]
    have he (j : Fin m) : (∑ l,fourthGreenTubeCoefficient u b (j,l))=
        |A j|+∑ l∈Finset.univ.erase j,|B j l| := by
      rw [← Finset.sum_erase_add Finset.univ (fun l => fourthGreenTubeCoefficient u b (j,l)) (Finset.mem_univ j),hdiag]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      exact fourthGreenTubeCoefficient_off_diagonal u b j l (Ne.symm (Finset.mem_erase.mp hl).1) (hu j) (hu l) (hreg j)
    simp_rw [he]
    rw [Finset.sum_add_distrib]
  rw [hsum,hardGaussianWeightedFacetIntegral_pairing_of_slack u b hu hreg]
  change |(∑ j,A j)-(1/2:ℝ)*(∑ j,∑ l∈Finset.univ.erase j,B j l)|≤_
  have hb : |∑ j,∑ l∈Finset.univ.erase j,B j l|≤∑ j,∑ l∈Finset.univ.erase j,|B j l| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
  have hb0 : 0≤∑ j,∑ l∈Finset.univ.erase j,|B j l| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  calc
    _ ≤ |∑ j,A j|+(1/2:ℝ)*|∑ j,∑ l∈Finset.univ.erase j,B j l| := by
      simpa only [abs_mul,show |(1/2:ℝ)|=1/2 by norm_num] using abs_sub (∑ j,A j) ((1/2:ℝ)*(∑ j,∑ l∈Finset.univ.erase j,B j l))
    _ ≤ (∑ j,|A j|)+(1/2:ℝ)*(∑ j,∑ l∈Finset.univ.erase j,|B j l|) :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ ≤ _ := by linarith

/-- Genuine localized weighted facet surface estimate, with the actual
three-face radius and no assumed surface or radius supplier. -/
theorem abs_hardGaussianWeightedFacetIntegral_le_threeFace_tube {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ j,ResidualThresholdRegularity (fun k => U (f k)) b j) :
    |hardGaussianWeightedFacetIntegral (fun k => U (f k)) b|≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,(fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) :=
  (abs_hardGaussianWeightedFacetIntegral_le_coefficient_sum _ b hu hreg).trans
    (fourthGreenTubeCoefficient_sum_le_threeFaceRadius hp U f b hu hreg)

end
end RectangleCLTArxivV1

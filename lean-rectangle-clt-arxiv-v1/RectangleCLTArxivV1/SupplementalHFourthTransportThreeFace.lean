import RectangleCLTArxivV1.SupplementalHFourthTransportSum
import RectangleCLTArxivV1.SupplementalHFourthTransportFacet
import RectangleCLTArxivV1.SupplementalHFourthTransportSlack
import RectangleCLTArxivV1.SupplementalHRadius

/-! The common radius is the actual maximum over spans of at most three
signed faces. No normal-space norm bound is an endpoint premise. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def fourthThreeFaceRadius {p r : ℕ} (U : Face p → Vector r) (x : EuclideanSpace ℝ (Fin r)) : ℝ :=
  supplementalHRadius U (fun j => x j)

theorem continuous_fourthThreeFaceRadius {p r : ℕ} (U : Face p → Vector r) :
    Continuous (fourthThreeFaceRadius U) := by
  change Continuous (fun x : EuclideanSpace ℝ (Fin r) =>
    1+‖fun f : Fin 3 → Face p => ‖(threeFaceSubspace U f).orthogonalProjection x‖‖)
  exact continuous_const.add (Continuous.norm (continuous_pi (fun f =>
    (threeFaceSubspace U f).orthogonalProjection.continuous.norm)))

theorem fourthThreeFaceRadius_ge_one {p r : ℕ} (U : Face p → Vector r)
    (x : EuclideanSpace ℝ (Fin r)) : 1≤fourthThreeFaceRadius U x := supplementalHRadius_ge_one U _

theorem fourthThreeFaceRadius_add_le {p r : ℕ} (U : Face p → Vector r)
    (x d : EuclideanSpace ℝ (Fin r)) : fourthThreeFaceRadius U (x+d)≤fourthThreeFaceRadius U x+‖d‖ := by
  exact supplementalHRadius_add_le U (fun j => x j) (fun j => d j)

theorem fourthThreeFaceRadius_fourth_integrable {p r : ℕ} (hp : 1≤p) (U : Face p → Vector r) :
    Integrable (fun g => fourthTransportRadius (fourthThreeFaceRadius U) g^4) (standardGaussian r) :=
  (supplementalHRadius_moment_le hp U 4).1

theorem supplementalHRadius_abs_inner_small_span_le {p r q : ℕ} (hp : 1≤p)
    (U : Face p → Vector r) (f : Fin q → Face p) (hq : q≤3)
    (d : EuclideanSpace ℝ (Fin r))
    (hd : d∈Submodule.span ℝ (range (fun i => projectionEuclideanVector (U (f i))))) (g : Vector r) :
    |⟪d,projectionEuclideanVector g⟫_ℝ|≤‖d‖*supplementalHRadius U g := by
  let S := Submodule.span ℝ (range (fun i => projectionEuclideanVector (U (f i))))
  let v : S := ⟨d,hd⟩
  have he : ⟪d,projectionEuclideanVector g⟫_ℝ=
      ⟪v,S.orthogonalProjection (projectionEuclideanVector g)⟫_ℝ := by
    rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]
  rw [he]
  exact (abs_real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left
    (supplementalHRadius_small_span_norm_le hp U f hq g) (norm_nonneg _))

theorem supplementalHRadius_face_abs_le {p r : ℕ} (hp : 1≤p) (U : Face p → Vector r)
    (f : Face p) (hu : vectorNormSq (U f)=1) (g : Vector r) :
    |faceDot (U f) g|≤supplementalHRadius U g := by
  have hh := supplementalHRadius_abs_inner_small_span_le hp U (fun _ : Fin 1 => f) (by norm_num)
    (projectionEuclideanVector (U f)) (Submodule.subset_span ⟨0,rfl⟩) g
  rw [thresholdEuclideanNormal_unit _ hu,one_mul] at hh
  have he : faceDot (U f) g=⟪projectionEuclideanVector (U f),projectionEuclideanVector g⟫_ℝ :=
    faceDot_eq_euclidean_inner _ _
  rw [← he] at hh
  exact hh

/-- The true bisector normal-space point lies in the selected two-face
span and has exactly its two Gaussian normal coordinates. -/
theorem fourthRidgeNormalPoint_norm_le_threeFaceRadius {p m r : ℕ} (hpfaces : 1≤p)
    (U : Face p → Vector r) (f : Fin m → Face p) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (U (f j))=1) (hv : vectorNormSq (U (f l))=1)
    (hp : projectionEuclideanVector (U (f j))+projectionEuclideanVector (U (f l))≠0)
    (hm : projectionEuclideanVector (U (f j))-projectionEuclideanVector (U (f l))≠0) (g : Vector r) :
    ‖fourthRidgeNormalPoint (fun k => U (f k)) b j l‖≤
      supplementalHRadius U (gaussianPairBase (fun k => U (f k)) b j l g) := by
  let u := fun k => U (f k)
  let A := projectionEuclideanVector (u j)
  let B := projectionEuclideanVector (u l)
  let e := bisector A B
  let d := differenceDirection A B
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  let z := fourthRidgeNormalPoint u b j l
  let x := gaussianPairBase u b j l g
  let S := Submodule.span ℝ (range (fun i : Fin 2 => projectionEuclideanVector (U (![f j,f l] i))))
  have hA : ‖A‖=1 := thresholdEuclideanNormal_unit _ hu
  have hB : ‖B‖=1 := thresholdEuclideanNormal_unit _ hv
  have he : ‖e‖=1 := norm_bisector _ _ hp
  have hd : ‖d‖=1 := norm_differenceDirection _ _ hm
  have hed : ⟪e,d⟫_ℝ=0 := inner_bisector_differenceDirection _ _ (hA.trans hB.symm)
  have hAmem : A∈S := Submodule.subset_span ⟨0,rfl⟩
  have hBmem : B∈S := Submodule.subset_span ⟨1,rfl⟩
  have hemem : e∈S := S.smul_mem _ (S.add_mem hAmem hBmem)
  have hdmem : d∈S := S.smul_mem _ (S.sub_mem hAmem hBmem)
  have hz : z=a • e+c • d := by
    change fourthRidgeNormalPoint u b j l=a • e+c • d
    rw [fourthRidgeNormalPoint,thresholdPairBisector_euclidean,thresholdPairDifference_euclidean]
  have hzmem : z∈S := by rw [hz]; exact S.add_mem (S.smul_mem _ hemem) (S.smul_mem _ hdmem)
  have hlevels := gaussianPairBase_frame_levels u b j l hu hv hp hm g
  have hxe : ⟪e,projectionEuclideanVector x⟫_ℝ=a := by
    have heq : faceDot (thresholdPairBisector u j l) x=
        ⟪projectionEuclideanVector (thresholdPairBisector u j l),projectionEuclideanVector x⟫_ℝ :=
      faceDot_eq_euclidean_inner _ _
    rw [thresholdPairBisector_euclidean] at heq
    exact heq.symm.trans hlevels.1
  have hxd : ⟪d,projectionEuclideanVector x⟫_ℝ=c := by
    have heq : faceDot (thresholdPairDifference u j l) x=
        ⟪projectionEuclideanVector (thresholdPairDifference u j l),projectionEuclideanVector x⟫_ℝ :=
      faceDot_eq_euclidean_inner _ _
    rw [thresholdPairDifference_euclidean] at heq
    exact heq.symm.trans hlevels.2
  have hzx : ⟪z,projectionEuclideanVector x⟫_ℝ=‖z‖^2 := by
    rw [hz,inner_add_left,inner_smul_left,inner_smul_left,conj_trivial,hxe,hxd,norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,he,hd,mul_one,sq_abs,inner_smul_left,inner_smul_right,
      conj_trivial,hed,mul_zero,zero_mul,add_zero]
    ring
  have hh := supplementalHRadius_abs_inner_small_span_le hpfaces U ![f j,f l] (by norm_num) z hzmem x
  rw [hzx,abs_of_nonneg (sq_nonneg _)] at hh
  change ‖z‖≤supplementalHRadius U x
  by_cases hz0 : ‖z‖=0
  · rw [hz0]
    exact (supplementalHRadius_pos U x).le
  · have hzpos : 0<‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
    have hmul : ‖z‖*‖z‖≤‖z‖*supplementalHRadius U x := by simpa only [pow_two] using hh
    exact le_of_mul_le_mul_left hmul hzpos


/-- The actual three-face radius discharges every radius and moment input
of the global disjoint facet/ridge transport. -/
theorem fourthGreenTubeCoefficient_sum_le_threeFaceRadius {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (b : Vector m)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ j,ResidualThresholdRegularity (fun k => U (f k)) b j) :
    (∑ q : Fin m × Fin m,fourthGreenTubeCoefficient (fun k => U (f k)) b q)≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,(fourthOuterLayer (fun k => U (f k)) b (fourthThreeFaceRadius U)).indicator
        (fun g => supplementalHRadius U g^4) g ∂standardGaussian (n+1)) := by
  exact fourthGreenTubeCoefficient_sum_le (fun k => U (f k)) b hu hreg
    (fourthThreeFaceRadius U) (continuous_fourthThreeFaceRadius U) (fourthThreeFaceRadius_ge_one U)
    (fourthThreeFaceRadius_add_le U)
    (fun j x => supplementalHRadius_face_abs_le hp U (f j) (hu j) x)
    (fun j l hplus hminus z => fourthRidgeNormalPoint_norm_le_threeFaceRadius hp U f b j l
      (hu j) (hu l) hplus hminus z)
    (fourthThreeFaceRadius_fourth_integrable hp U)

/-- Genuine change from standardized threshold coordinates to the actual
independent-base/Gaussian outward event, retaining the same radius. -/
theorem fourthOuterLayer_shift_threshold {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (x : Vector r) {σ : ℝ} (hσ : 0<σ)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (g : Vector r) :
    g∈fourthOuterLayer u (fun j => (a j-faceDot (u j) x)/σ) R ↔
      (x,g)∈gaussianOutwardVariableTube u a σ (fourthTransportRadius R) := by
  have he (j : Fin m) (d : ℝ) :
      faceDot (u j) (x+σ • g)≤a j+σ*d ↔
        faceDot (u j) g≤(a j-faceDot (u j) x)/σ+d := by
    rw [show (a j-faceDot (u j) x)/σ+d=(a j-faceDot (u j) x+σ*d)/σ by field_simp; ring,
      le_div_iff₀ hσ,threshold_faceDot_add_right,threshold_faceDot_smul_right]
    constructor <;> intro h <;> linarith
  change ((∀ j,faceDot (u j) g≤(a j-faceDot (u j) x)/σ+1/fourthTransportRadius R g) ∧
      ¬∀ j,faceDot (u j) g≤(a j-faceDot (u j) x)/σ) ↔
    ((∀ j,faceDot (u j) (x+σ • g)≤a j+σ/fourthTransportRadius R g) ∧
      ¬∀ j,faceDot (u j) (x+σ • g)≤a j+0)
  have houter : (∀ j,faceDot (u j) (x+σ • g)≤a j+σ/fourthTransportRadius R g) ↔
      ∀ j,faceDot (u j) g≤(a j-faceDot (u j) x)/σ+1/fourthTransportRadius R g := by
    simpa only [mul_one_div] using forall_congr' (fun j => he j (1/fourthTransportRadius R g))
  have hinner : (∀ j,faceDot (u j) (x+σ • g)≤a j+0) ↔
      ∀ j,faceDot (u j) g≤(a j-faceDot (u j) x)/σ := by
    simpa only [mul_zero,add_zero] using forall_congr' (fun j => he j 0)
  rw [houter,hinner]

/-- Pointwise actual threshold/base version, ready for the independent-base
concentration Fubini estimate. Its only regularity input is ordinary slack. -/
theorem fourthGreenTubeCoefficient_affine_sum_le {p m n : ℕ} (hp : 1≤p)
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m) (x : Vector (n+1))
    {σ : ℝ} (hσ : 0<σ) (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ j,ResidualThresholdRegularity (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) j) :
    (∑ q : Fin m × Fin m,fourthGreenTubeCoefficient (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) q)≤
      (16384*Real.exp ((3:ℝ)/2))*(∫ g,(gaussianOutwardVariableTube (fun k => U (f k)) a σ
        (supplementalHRadius U)).indicator (fun z => supplementalHRadius U z.2^4) (x,g) ∂standardGaussian (n+1)) := by
  have hh := fourthGreenTubeCoefficient_sum_le_threeFaceRadius hp U f
    (fun k => (a k-faceDot (U (f k)) x)/σ) hu hreg
  apply hh.trans_eq
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    have he := fourthOuterLayer_shift_threshold (fun k => U (f k)) a x hσ (fourthThreeFaceRadius U) g
    change g∈fourthOuterLayer (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) (fourthThreeFaceRadius U) ↔
      (x,g)∈gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U) at he
    by_cases hg : g∈fourthOuterLayer (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ) (fourthThreeFaceRadius U)
    · rw [indicator_of_mem hg,indicator_of_mem (he.mp hg)]
    · rw [indicator_of_not_mem hg,indicator_of_not_mem (fun h => hg (he.mpr h))])

end
end RectangleCLTArxivV1

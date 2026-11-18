import RectangleCLTArxivV1.SupplementalHNonsimpleActualMass
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenMass

/-! The native leading ridge term has the canonical Gaussian mass and
normal-space point of its actual codimension-two face. All original hard
inequalities are retained. No full-family independence is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def nonsimpleNativePairFrame {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) :
    Fin 2 → EuclideanSpace ℝ (Fin r) :=
  ![(WithLp.equiv 2 (Vector r)).symm (thresholdPairBisector u j l),
    (WithLp.equiv 2 (Vector r)).symm (thresholdPairDifference u j l)]

def nonsimpleNativePairLevels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : Fin 2 → ℝ :=
  ![thresholdPairFirstLevel u b j l, thresholdPairSecondLevel u b j l]

def nonsimpleNativePairPoint {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : EuclideanSpace ℝ (Fin r) :=
  ∑ a, nonsimpleNativePairLevels u b j l a • nonsimpleNativePairFrame u j l a

theorem nonsimpleNativePairFrame_orthonormal {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) :
    Orthonormal ℝ (nonsimpleNativePairFrame u j l) := by
  have he : faceDot (thresholdPairBisector u j l) (thresholdPairBisector u j l) = 1 := by
    simpa only [faceDot, vectorNormSq, pow_two] using thresholdPairBisector_unit u j l hp.1
  have hf : faceDot (thresholdPairDifference u j l) (thresholdPairDifference u j l) = 1 := by
    simpa only [faceDot, vectorNormSq, pow_two] using thresholdPairDifference_unit u j l hp.2
  have hef := thresholdPair_frame_orthogonal u j l hu hv
  have hfe : faceDot (thresholdPairDifference u j l) (thresholdPairBisector u j l) = 0 := by
    rw [faceDot_comm]
    exact hef
  simp only [faceDot] at he hf hef hfe
  rw [orthonormal_iff_ite]
  intro a d
  fin_cases a <;> fin_cases d <;>
    simp [nonsimpleNativePairFrame, ← faceDot_eq_euclidean_inner, he, hf, hef, hfe]

/-- The native pair section is the actual orthonormal frame section. -/
theorem gaussianFrameSectionPoint_nonsimpleNativePair {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) (g : Vector r) :
    WithLp.equiv 2 (Vector r) (gaussianFrameSectionPoint (nonsimpleNativePairFrame u j l)
      (nonsimpleNativePairLevels u b j l) ((WithLp.equiv 2 (Vector r)).symm g)) =
      gaussianPairBase u b j l g := by
  rw [gaussianPairBase, gaussianPairSectionPoint_orthogonal_formula _ _
    (thresholdPair_frame_orthogonal u j l hu hv)]
  simp only [gaussianFrameSectionPoint, gaussianFrameProjection, nonsimpleNativePairFrame,
    nonsimpleNativePairLevels, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons, ← faceDot_eq_euclidean_inner,
    WithLp.equiv_add, WithLp.equiv_sub, WithLp.equiv_smul, Equiv.apply_symm_apply]
  ext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem nonsimpleNativePairFrame_span_actualFace {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hactive : R.1 = {j, l}) :
    Submodule.span ℝ (Set.range (nonsimpleNativePairFrame u j l)) =
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) R.1 := by
  classical
  let S := nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) R.1
  have hj : nonsimpleNativeNormals u j ∈ S := nonsimple_normal_mem _ _ j (by rw [hactive]; simp)
  have hl : nonsimpleNativeNormals u l ∈ S := nonsimple_normal_mem _ _ l (by rw [hactive]; simp)
  have he : (WithLp.equiv 2 (Vector r)).symm (thresholdPairBisector u j l) ∈ S := by
    change (WithLp.equiv 2 (Vector r)).symm
      (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖⁻¹ • (u j + u l)) ∈ S
    rw [WithLp.equiv_symm_smul, WithLp.equiv_symm_add]
    exact S.smul_mem _ (S.add_mem hj hl)
  have hf : (WithLp.equiv 2 (Vector r)).symm (thresholdPairDifference u j l) ∈ S := by
    change (WithLp.equiv 2 (Vector r)).symm
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖⁻¹ • (u j - u l)) ∈ S
    rw [WithLp.equiv_symm_smul, WithLp.equiv_symm_sub]
    exact S.smul_mem _ (S.sub_mem hj hl)
  have hle : Submodule.span ℝ (Set.range (nonsimpleNativePairFrame u j l)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · exact he
    · exact hf
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card (nonsimpleNativePairFrame_orthonormal u j l hu hv hp).linearIndependent,
    R.2.2]
  simp only [Fintype.card_fin]

theorem nonsimpleNativePairPoint_native {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) :
    WithLp.equiv 2 (Vector r) (nonsimpleNativePairPoint u b j l) = gaussianPairBase u b j l 0 := by
  have h := gaussianFrameSectionPoint_nonsimpleNativePair u b j l hu hv (0 : Vector r)
  simpa only [WithLp.equiv_symm_zero, gaussianFrameSectionPoint, gaussianFrameProjection,
    inner_zero_right, zero_smul, Finset.sum_const_zero, add_zero, sub_zero,
    nonsimpleNativePairPoint] using h

private theorem nonsimple_pair_native_inner {r : ℕ} (v : Vector r)
    (x : EuclideanSpace ℝ (Fin r)) :
    ⟪(WithLp.equiv 2 (Vector r)).symm v, x⟫_ℝ =
      faceDot v (WithLp.equiv 2 (Vector r) x) := by
  rw [faceDot_eq_euclidean_inner]
  rfl

theorem nonsimpleNativePairPoint_supporting_levels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l) :
    ⟪nonsimpleNativeNormals u j, nonsimpleNativePairPoint u b j l⟫_ℝ = b j ∧
      ⟪nonsimpleNativeNormals u l, nonsimpleNativePairPoint u b j l⟫_ℝ = b l := by
  rw [show nonsimpleNativeNormals u j = (WithLp.equiv 2 (Vector r)).symm (u j) from rfl,
    show nonsimpleNativeNormals u l = (WithLp.equiv 2 (Vector r)).symm (u l) from rfl,
    nonsimple_pair_native_inner, nonsimple_pair_native_inner,
    nonsimpleNativePairPoint_native u b j l hu hv]
  exact ⟨gaussianPairBase_left_level u b j l hu hv hp.1 hp.2 0,
    gaussianPairBase_right_level u b j l hu hv hp.1 hp.2 0⟩

theorem nonsimpleNativePairPoint_eq_actualFaceNormalPoint {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hactive : R.1 = {j, l}) :
    nonsimpleNativePairPoint u b j l = nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b R := by
  classical
  have hspan := nonsimpleNativePairFrame_span_actualFace u b j l hu hv hp R hactive
  have hzmem : nonsimpleNativePairPoint u b j l ∈
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) R.1 := by
    rw [← hspan]
    exact Submodule.sum_mem _ (fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  apply nonsimpleFaceNormalPoint_unique (nonsimpleNativeNormals u) b R.1 _ _ hzmem
    (nonsimpleFaceNormalPoint_mem _ _ R)
  have hlevels := nonsimpleNativePairPoint_supporting_levels u b j l hu hv hp
  intro k hk
  rw [nonsimpleFaceNormalPoint_levels _ _ R k hk]
  have hmem : k = j ∨ k = l := by simpa only [hactive, Finset.mem_insert, Finset.mem_singleton] using hk
  rcases hmem with rfl | rfl
  · exact hlevels.1
  · exact hlevels.2

theorem nonsimpleNativePair_normalLength_eq_actualFaceNormalPoint_normSq {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hactive : R.1 = {j, l}) :
    (thresholdPairFirstLevel u b j l)^2 + (thresholdPairSecondLevel u b j l)^2 =
      ‖nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b R‖^2 := by
  have h := gaussianFrame_normalPoint_normSq (nonsimpleNativePairFrame u j l)
    (nonsimpleNativePairFrame_orthonormal u j l hu hv hp) (nonsimpleNativePairLevels u b j l)
  change ‖nonsimpleNativePairPoint u b j l‖^2 = _ at h
  rw [nonsimpleNativePairPoint_eq_actualFaceNormalPoint u b j l hu hv hp R hactive] at h
  simpa only [nonsimpleNativePairLevels, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h.symm

/-- The two native normal densities times the actual retained pair
section probability equal the canonical full-original-event ridge mass. -/
theorem nonsimpleNativePair_mass_eq_actualFaceMass {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hactive : R.1 = {j, l}) :
    (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)) *
      hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) =
      nonsimpleActualGaussianMass u b R := by
  have hprob : hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
      (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) =
      (standardGaussian r).real {g | gaussianPairBase u b j l g ∈
        gaussianFiniteThresholdEvent Finset.univ u b} := by
    rw [hardGaussianPairSectionProbability_eq_residual_CDF _ u b _ _ _ _
      (thresholdPair_frame_orthogonal u j l hu hv)]
    unfold gaussianFiniteThresholdCDF
    congr 1
    ext g
    exact (gaussianPairBase_mem_full_event_iff_residual u b j l hu hv hp g).symm
  have hmass : (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)) *
      hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) =
      gaussianFrameHardMass Finset.univ u b (nonsimpleNativePairFrame u j l)
        (nonsimpleNativePairLevels u b j l) := by
    rw [hprob]
    unfold gaussianFrameHardMass
    simp_rw [gaussianFrameSectionPoint_nonsimpleNativePair u b j l hu hv]
    simp only [nonsimpleNativePairLevels, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hmass]
  apply gaussianFrameHardMass_eq_actualFaceMass u b R _
    (nonsimpleNativePairFrame_orthonormal u j l hu hv hp) _
    (nonsimpleNativePairFrame_span_actualFace u b j l hu hv hp R hactive)
  intro k hk
  change ⟪nonsimpleNativeNormals u k, nonsimpleNativePairPoint u b j l⟫_ℝ = b k
  rw [nonsimpleNativePairPoint_eq_actualFaceNormalPoint u b j l hu hv hp R hactive]
  exact nonsimpleFaceNormalPoint_levels _ _ R k hk

/-- The exact leading term of the actual ridge, before any ordered-pair
counting or geometric choice of an angle notation. -/
theorem hardGaussianRidgeLeadingTerm_eq_actualFace {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : hardGaussianRidgeNonparallel u j l)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) (hactive : R.1 = {j, l}) :
    hardGaussianRidgeLeadingTerm u b j l =
      Real.arccos (faceDot (u j) (u l)) *
        (‖nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b R‖^2 - 2) *
        nonsimpleActualGaussianMass u b R := by
  classical
  rw [hardGaussianRidgeLeadingTerm, if_pos hp]
  unfold hardGaussianRidgeNormalWeight
  have hmass := nonsimpleNativePair_mass_eq_actualFaceMass u b j l hu hv hp R hactive
  have hnorm := nonsimpleNativePair_normalLength_eq_actualFaceNormalPoint_normSq u b j l hu hv hp R hactive
  calc
    _ = Real.arccos (faceDot (u j) (u l)) *
        ((thresholdPairFirstLevel u b j l)^2 + (thresholdPairSecondLevel u b j l)^2 - 2) *
        ((gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
          gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)) *
          hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
            (thresholdPairBisector u j l) (thresholdPairDifference u j l)
            (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) := by ring
    _ = _ := by rw [hmass, hnorm]

end
end RectangleCLTArxivV1

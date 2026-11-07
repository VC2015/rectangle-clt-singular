import RectangleCLTCompanion.SplitV4.GaussianPairSections
import RectangleCLTCompanion.SplitV4.GaussianThresholdTubeGeometry
import RectangleCLTCompanion.SplitV4.GaussianThresholdAPI

/-! The actual mixed hard-Gaussian derivative in the symmetric bisector
frame. Conditional Gaussian sections are identified pointwise, and the
two-dimensional Gaussian density is preserved by the orthonormal rotation. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology InnerProductSpace

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem thresholdPair_sum_sub_ne_zero_of_independent {m r : ℕ}
    (u : Fin m → Vector r) (hi : LinearIndependent ℝ u) (j l : Fin m) (hjl : j ≠ l) :
    projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0 ∧
      projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0 := by
  constructor
  · intro hz
    have hn : u j + u l = 0 := by
      ext k
      have hk := congrArg (fun z : EuclideanSpace ℝ (Fin r) => z k) hz
      simpa using hk
    have he : (1 : ℝ) • u j = (-1 : ℝ) • u l := by
      ext k
      have hk := congrFun hn k
      simp only [Pi.add_apply, Pi.zero_apply] at hk
      simp only [Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul]
      linarith
    exact hjl (hi.eq_of_smul_apply_eq_smul_apply 1 (-1) j l (by norm_num) he)
  · intro hz
    have hn : u j - u l = 0 := by
      ext k
      have hk := congrArg (fun z : EuclideanSpace ℝ (Fin r) => z k) hz
      simpa using hk
    exact hjl (hi.injective (sub_eq_zero.mp hn))

def gaussianPairConditionalDirection {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) : Vector r :=
  (gaussianThresholdResidualScale u j l)⁻¹ • gaussianNormalProjection (u j) (u l)

def gaussianPairConditionalLevel {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  (b l - b j * faceDot (u l) (u j)) / gaussianThresholdResidualScale u j l

def gaussianPairConditionalBase {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (g : Vector r) : Vector r :=
  gaussianPairSectionPoint (u j) (gaussianPairConditionalDirection u j l) (b j)
    (gaussianPairConditionalLevel u b j l) g

theorem gaussianPair_coordinate_rotation_levels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    thresholdPairFirstCoefficient u j l * b j +
        thresholdPairSecondCoefficient u j l * gaussianPairConditionalLevel u b j l = thresholdPairFirstLevel u b j l ∧
      thresholdPairSecondCoefficient u j l * b j -
        thresholdPairFirstCoefficient u j l * gaussianPairConditionalLevel u b j l = thresholdPairSecondLevel u b j l := by
  let A := thresholdPairFirstCoefficient u j l
  let B := thresholdPairSecondCoefficient u j l
  let α := thresholdPairFirstLevel u b j l
  let β := thresholdPairSecondLevel u b j l
  let q := gaussianPairConditionalDirection u j l
  let x := gaussianPairBase u b j l 0
  have hframe := gaussianPairBase_frame_levels u b j l hu hv hp hm 0
  have hj := gaussianPairBase_left_level u b j l hu hv hp hm 0
  have hl := gaussianPairBase_right_level u b j l hu hv hp hm 0
  have hleft : A * α + B * β = b j := by
    rw [thresholdPair_left_expansion u j l hp hm, faceDot_affine_combination, hframe.1, hframe.2] at hj
    exact hj
  have hq : faceDot q x = gaussianPairConditionalLevel u b j l := by
    dsimp only [q, gaussianPairConditionalDirection]
    rw [threshold_faceDot_smul_left, gaussianNormalProjection, threshold_faceDot_sub_left,
      threshold_faceDot_smul_left]
    change (gaussianThresholdResidualScale u j l)⁻¹ *
      (faceDot (u l) (gaussianPairBase u b j l 0) -
        faceDot (u l) (u j) * faceDot (u j) (gaussianPairBase u b j l 0)) = _
    rw [hl, hj]
    unfold gaussianPairConditionalLevel
    ring
  have hright : B * α - A * β = gaussianPairConditionalLevel u b j l := by
    have hqe := thresholdPair_residualNormal_eq u j l hu hv hp hm
    change q = B • thresholdPairBisector u j l - A • thresholdPairDifference u j l at hqe
    rw [hqe, threshold_faceDot_sub_left, threshold_faceDot_smul_left,
      threshold_faceDot_smul_left] at hq
    change B * faceDot (thresholdPairBisector u j l) (gaussianPairBase u b j l 0) -
        A * faceDot (thresholdPairDifference u j l) (gaussianPairBase u b j l 0) = _ at hq
    rw [hframe.1, hframe.2] at hq
    exact hq
  have hab := (thresholdPair_coefficients_sq u j l hu hv).1
  change A ^ 2 + B ^ 2 = 1 at hab
  constructor
  · change A * b j + B * gaussianPairConditionalLevel u b j l = α
    rw [← hleft, ← hright]
    calc
      _ = (A ^ 2 + B ^ 2) * α := by ring
      _ = α := by rw [hab, one_mul]
  · change B * b j - A * gaussianPairConditionalLevel u b j l = β
    rw [← hleft, ← hright]
    calc
      _ = (A ^ 2 + B ^ 2) * β := by ring
      _ = β := by rw [hab, one_mul]

theorem gaussianPairConditionalBase_eq_pairBase {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) (g : Vector r) :
    gaussianPairConditionalBase u b j l g = gaussianPairBase u b j l g := by
  have horth : faceDot (u j) (gaussianPairConditionalDirection u j l) = 0 := by
    rw [gaussianPairConditionalDirection, threshold_faceDot_smul_right,
      gaussianNormalProjection_orthogonal (u j) (u l) hu, mul_zero]
  have hchange := gaussianPairSectionPoint_change_frame
    (thresholdPairBisector u j l) (thresholdPairDifference u j l) (u j) (gaussianPairConditionalDirection u j l)
    (thresholdPair_frame_orthogonal u j l hu hv) horth
    (thresholdPairFirstCoefficient u j l) (thresholdPairSecondCoefficient u j l)
    (thresholdPair_coefficients_sq u j l hu hv).1
    (thresholdPair_left_expansion u j l hp hm) (thresholdPair_residualNormal_eq u j l hu hv hp hm)
    (b j) (gaussianPairConditionalLevel u b j l) g
  have hlevels := gaussianPair_coordinate_rotation_levels u b j l hu hv hp hm
  rw [hlevels.1, hlevels.2] at hchange
  exact hchange

theorem gaussianPair_conditional_density_eq {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    gaussianPDFReal 0 1 (b j) * gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l) =
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) := by
  have hd := gaussianPair_rotation_preserves_density
    (thresholdPairFirstCoefficient u j l) (thresholdPairSecondCoefficient u j l)
    (b j) (gaussianPairConditionalLevel u b j l) (thresholdPair_coefficients_sq u j l hu hv).1
  have hl := gaussianPair_coordinate_rotation_levels u b j l hu hv hp hm
  rw [hl.1, hl.2] at hd
  exact hd

/-- The actual mixed coordinate derivative in the symmetric two-normal
frame, with the exact inverse Gram-Jacobian and strict inactive section. -/
theorem gaussianThresholdMixed_eq_pairBase {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdMixed u b j l =
      (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) /
          Real.sqrt (1 - faceDot (u j) (u l) ^ 2)) *
        (standardGaussian r).real {g | ∀ k, k ≠ j → k ≠ l →
          faceDot (u k) (gaussianPairBase u b j l g) < b k} := by
  classical
  obtain ⟨hp, hm⟩ := thresholdPair_sum_sub_ne_zero_of_independent u hi j l hjl
  let s := (Finset.univ.erase j).erase l
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  let σ := gaussianThresholdResidualScale u j l
  let q := gaussianPairConditionalDirection u j l
  let c := gaussianPairConditionalLevel u b j l
  have hproj (k : Fin m) (hk : k ∈ s) : gaussianNormalProjection q (v k) ≠ 0 :=
    gaussianNormalProjection_twice_ne_zero_of_independent u hi j l k
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1 _
  have hprob : gaussianThresholdSectionProbability s v d q c =
      (standardGaussian r).real {g | ∀ k, k ≠ j → k ≠ l →
        faceDot (u k) (gaussianPairBase u b j l g) < b k} := by
    rw [gaussianFiniteSectionProbability_eq_strict s v d q c hproj]
    congr 1
    ext g
    have hdot (k : Fin m) : faceDot (u k) (gaussianPairBase u b j l g) =
        b j * faceDot (u k) (u j) + faceDot (v k) (SignedSurface.gaussianSectionPoint q c g) := by
      rw [← gaussianPairConditionalBase_eq_pairBase u b j l hu hv hp hm g]
      exact gaussianSectionPoint_faceDot (u j) (u k) (SignedSurface.gaussianSectionPoint q c g) (b j)
    constructor
    · intro h k hkj hkl
      have hk := h k (Finset.mem_erase.mpr ⟨hkl, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩⟩)
      change faceDot (v k) (SignedSurface.gaussianSectionPoint q c g) < b k - b j * faceDot (u k) (u j) at hk
      rw [hdot]
      linarith
    · intro h k hk
      have hk' := h k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1
      rw [hdot] at hk'
      change faceDot (v k) (SignedSurface.gaussianSectionPoint q c g) < b k - b j * faceDot (u k) (u j)
      linarith
  rw [gaussianThresholdMixed_eq_two_normal_section u b j l hjl hu hi]
  change gaussianPDFReal 0 1 (b j) * ((gaussianPDFReal 0 1 c / σ) *
    gaussianThresholdSectionProbability s v d q c) = _
  rw [hprob]
  have hdens := gaussianPair_conditional_density_eq u b j l hu hv hp hm
  have hscale := gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv
  calc
    _ = (gaussianPDFReal 0 1 (b j) * gaussianPDFReal 0 1 c / σ) *
        (standardGaussian r).real {g | ∀ k, k ≠ j → k ≠ l → faceDot (u k) (gaussianPairBase u b j l g) < b k} := by ring
    _ = _ := by
      rw [hdens]
      dsimp only [σ]
      rw [hscale]

end
end RectangleCLT.Companion.SplitV4

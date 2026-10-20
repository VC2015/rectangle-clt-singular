import RectangleCLTCompanion.SignedSurfaceCoefficients
import RectangleCLTCompanion.SignedSurfaceLocalization

/-! Compatibility of the bisector domain with the actual augmented
Gaussian tube map, including its exact determinant/volume cancellation. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def euclideanNormal {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (f : Face p) :
    EuclideanSpace ℝ (Fin p) := projectionEuclideanVector (signedRowNormal A f)

theorem euclideanNormal_unit {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (f : Face p) : ‖euclideanNormal A f‖ = 1 := by
  simpa only [euclideanNormal, Real.sqrt_one] using
    signedRowNormal_euclidean_norm A (by norm_num : (0 : ℝ) ≤ 1) hdiag f

theorem euclideanNormal_inner {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (f g : Face p) :
    ⟪euclideanNormal A f, euclideanNormal A g⟫_ℝ =
      faceSign f * faceSign g * (A * A.transpose) f.1 g.1 := by
  calc
    _ = faceDot (signedRowNormal A f) (signedRowNormal A g) := by
      simp [euclideanNormal, projectionEuclideanVector, PiLp.inner_apply, faceDot, mul_comm]
    _ = _ := signedRowNormal_gram A f g

def pairTubeCoefficients {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ ε : ℝ) : Set (Fin 2 → ℝ) :=
  pairCoefficientDomain (euclideanNormal A (S.face 0)) (euclideanNormal A (S.face 1)) σ ε

theorem unitPair_det {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    (S.gram (A * A.transpose)).det =
      1 - ⟪euclideanNormal A (S.face 0), euclideanNormal A (S.face 1)⟫_ℝ ^ 2 := by
  have hsym : ∀ i j, (A * A.transpose) i j = (A * A.transpose) j i := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [Matrix.det_fin_two, S.gram_diagonal hdiag 0, S.gram_diagonal hdiag 1,
    S.gram_symmetric hsym 1 0, euclideanNormal_inner]
  unfold CompatibleFaceTuple.gram
  ring

theorem normalMatrix_scaled_gram_det {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) :
    ((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det =
      (σ ^ 2) ^ q * (S.gram (A * A.transpose)).det := by
  have hM : (normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A) =
      σ ^ 2 • S.gram (A * A.transpose) := by
    ext i j
    rw [← normalMatrix_gram S A]
    simp only [normalMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hM, Matrix.det_smul, Fintype.card_fin]

theorem pairTube_displacement_eq {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (c : Fin 2 → ℝ) :
    projectionEuclideanVector ((normalMatrix S (σ • A)).mulVec c) =
      σ • (c 0 • euclideanNormal A (S.face 0) + c 1 • euclideanNormal A (S.face 1)) := by
  ext j
  change ((normalMatrix S (σ • A)).mulVec c) j =
    σ * (c 0 * (signedRowNormal A (S.face 0)) j + c 1 * (signedRowNormal A (S.face 1)) j)
  simp only [normalMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul, signedRowNormal]
  ring

theorem unitPair_nondegenerate {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hdet : 0 < (S.gram (A * A.transpose)).det) :
    euclideanNormal A (S.face 0) + euclideanNormal A (S.face 1) ≠ 0 ∧
      euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1) ≠ 0 := by
  have hu := euclideanNormal_unit A hdiag (S.face 0)
  have hv := euclideanNormal_unit A hdiag (S.face 1)
  rw [unitPair_det S A hdiag] at hdet
  constructor
  · intro hh
    have hs := norm_add_sq_real (euclideanNormal A (S.face 0)) (euclideanNormal A (S.face 1))
    rw [hh, norm_zero, hu, hv] at hs
    nlinarith
  · intro hh
    have hs := norm_sub_sq_real (euclideanNormal A (S.face 0)) (euclideanNormal A (S.face 1))
    rw [hh, norm_zero, hu, hv] at hs
    nlinarith

theorem pairTubeCoefficients_positive {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hdet : 0 < (S.gram (A * A.transpose)).det) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) {c : Fin 2 → ℝ}
    (hc : c ∈ pairTubeCoefficients S A σ ε) : ∀ i, 0 < c i :=
  pairCoefficientDomain_positive _ _ (euclideanNormal_unit A hdiag _) (euclideanNormal_unit A hdiag _)
    (unitPair_nondegenerate S A hdiag hdet).1 (unitPair_nondegenerate S A hdiag hdet).2 hσ hε hc

theorem pairTubeCoefficients_displacement_le {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hdet : 0 < (S.gram (A * A.transpose)).det) (σ : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) {c : Fin 2 → ℝ} (hc : c ∈ pairTubeCoefficients S A σ ε) :
    ‖projectionEuclideanVector ((normalMatrix S (σ • A)).mulVec c)‖ ≤ ε := by
  rw [pairTube_displacement_eq]
  exact pairCoefficientDomain_displacement_norm_le _ _
    (euclideanNormal_unit A hdiag _) (euclideanNormal_unit A hdiag _)
    (unitPair_nondegenerate S A hdiag hdet).1 (unitPair_nondegenerate S A hdiag hdet).2 σ hε hc

theorem pairTubeCoefficients_real_volume {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hdet : 0 < (S.gram (A * A.transpose)).det) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 ≤ ε) :
    (volume : Measure (Fin 2 → ℝ)).real (pairTubeCoefficients S A σ ε) =
      (ε ^ 2 * ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ / 16) /
        (σ ^ 2 * Real.sqrt (S.gram (A * A.transpose)).det) := by
  rw [unitPair_det S A hdiag]
  exact pairCoefficientDomain_real_volume _ _ (euclideanNormal_unit A hdiag _) (euclideanNormal_unit A hdiag _)
    (unitPair_nondegenerate S A hdiag hdet).1 (unitPair_nondegenerate S A hdiag hdet).2 hσ hε

/-- Exact cancellation of the small pair determinant against the wide
coefficient domain. Only a positive determinant, not a lower bound, is used. -/
theorem pairTube_gram_mul_volume {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hdet : 0 < (S.gram (A * A.transpose)).det) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 ≤ ε) :
    ((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det *
      (volume : Measure (Fin 2 → ℝ)).real (pairTubeCoefficients S A σ ε) =
      σ ^ 2 * ε ^ 2 *
        ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
        Real.sqrt (S.gram (A * A.transpose)).det / 16 := by
  rw [normalMatrix_scaled_gram_det, pairTubeCoefficients_real_volume S A hdiag hdet hσ hε]
  let d : ℝ := Real.sqrt (S.gram (A * A.transpose)).det
  have hd : 0 < d := Real.sqrt_pos.mpr hdet
  have hd2 : (S.gram (A * A.transpose)).det = d ^ 2 := (Real.sq_sqrt hdet.le).symm
  change (σ ^ 2) ^ 2 * (S.gram (A * A.transpose)).det *
      ((ε ^ 2 * ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ / 16) /
        (σ ^ 2 * d)) = _
  rw [hd2]
  field_simp [hσ.ne', hd.ne']
  ring

theorem euclideanNormal_smul {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (σ : ℝ) (f : Face p) : euclideanNormal (σ • A) f = σ • euclideanNormal A f := by
  ext j
  change faceSign f * (σ * A f.1 j) = σ * (faceSign f * A f.1 j)
  ring

theorem normalSpan_smul {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    S.normalSpan (σ • A) = S.normalSpan A := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change euclideanNormal (σ • A) (S.face i) ∈ S.normalSpan A
    rw [euclideanNormal_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change euclideanNormal A (S.face i) ∈ S.normalSpan (σ • A)
    have heq : euclideanNormal A (S.face i) = σ⁻¹ • euclideanNormal (σ • A) (S.face i) := by
      rw [euclideanNormal_smul, smul_smul, inv_mul_cancel₀ hσ, one_smul]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def pairRidgeNumerator {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (z : Vector p) : ℝ :=
  (1 - faceDot (signedRowNormal A (S.face 0)) (signedRowNormal A (S.face 1))) *
    (faceDot (signedRowNormal A (S.face 0)) z + faceDot (signedRowNormal A (S.face 1)) z)

theorem pairRidgeNumerator_eq_euclidean {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (z : Vector p) :
    pairRidgeNumerator S A z = pairedRidgeNumerator
      (euclideanNormal A (S.face 0)) (euclideanNormal A (S.face 1)) (projectionEuclideanVector z) := by
  simp [pairRidgeNumerator, pairedRidgeNumerator, euclideanNormal,
    projectionEuclideanVector, PiLp.inner_apply, faceDot, mul_comm]

theorem pairRidgeNumerator_eq {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1) (z : Vector p) :
    pairRidgeNumerator S A z =
      ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
        Real.sqrt (S.gram (A * A.transpose)).det *
        ⟪bisector (euclideanNormal A (S.face 0)) (euclideanNormal A (S.face 1)),
          projectionEuclideanVector z⟫_ℝ := by
  rw [pairRidgeNumerator_eq_euclidean, pairedRidgeNumerator_eq _ _ _
    (euclideanNormal_unit A hdiag _) (euclideanNormal_unit A hdiag _), unitPair_det S A hdiag]

theorem pairRidgeNumerator_zero_of_det_zero {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hdet : (S.gram (A * A.transpose)).det = 0) (z : Vector p) :
    pairRidgeNumerator S A z = 0 := by
  rw [pairRidgeNumerator_eq S A hdiag, hdet, Real.sqrt_zero, mul_zero, zero_mul]

theorem pairRidgeNumerator_abs_le_radius {p : ℕ} (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hdet : 0 < (S.gram (A * A.transpose)).det) {σ : ℝ} (hσ : σ ≠ 0) (z : Vector p) :
    |pairRidgeNumerator S A z| ≤
      ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
        Real.sqrt (S.gram (A * A.transpose)).det * fourFaceProjectionRadius (σ • A) z := by
  have hspan : bisector (euclideanNormal A (S.face 0)) (euclideanNormal A (S.face 1)) ∈
      S.normalSpan (σ • A) := by
    rw [normalSpan_smul S A hσ]
    apply Submodule.smul_mem
    exact Submodule.add_mem _ (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩)
  have hb := S.abs_inner_normalSpan_le_projectionRadius (σ • A) (by decide) (by decide) hspan z
  rw [norm_bisector _ _ (unitPair_nondegenerate S A hdiag hdet).1, one_mul] at hb
  rw [pairRidgeNumerator_eq S A hdiag, abs_mul, abs_mul, abs_norm,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end
end RectangleCLT.Companion.SignedSurface

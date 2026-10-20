import RectangleCLT.GaussianSoftRecursion
import RectangleCLT.GaussianProjectionMaximum
import RectangleCLT.GaussianLocalDeterminants

/-! Bounds for the actual sparse dual normals. All inverses are local active
Gram inverses, and Gaussian linear factors are controlled by the genuine
threshold-independent projection radius. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT

noncomputable section

/-- Rayleigh lower bounds control inverse quadratic forms. The proof uses
only the defining inverse identity and finite Cauchy--Schwarz. -/
theorem inverse_quadratic_le_inv {q : ℕ} (G : Matrix (Fin q) (Fin q) ℝ)
    (hd : IsUnit G.det) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * vectorNormSq u ≤ matrixQuadratic G u)
    (b : Fin q → ℝ) (hb : vectorNormSq b ≤ 1) :
    faceDot b (G⁻¹.mulVec b) ≤ 1 / a := by
  let u := G⁻¹.mulVec b
  have hGu : G.mulVec u = b := by
    rw [show u = G⁻¹.mulVec b from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv G hd, Matrix.one_mulVec]
  have hquad : matrixQuadratic G u = faceDot b u := by
    have heq : matrixQuadratic G u = faceDot u (G.mulVec u) := by
      simp only [matrixQuadratic, faceDot, Matrix.mulVec, dotProduct,
        Finset.mul_sum, mul_assoc]
    rw [heq, hGu, faceDot_comm]
  have hlo := hlower u
  rw [hquad] at hlo
  have hcs : (faceDot b u) ^ 2 ≤ vectorNormSq u := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q)) b u
    change (faceDot b u) ^ 2 ≤ vectorNormSq b * vectorNormSq u at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right hb (vectorNormSq_nonneg u)).trans_eq (one_mul _))
  have hr0 : 0 ≤ faceDot b u := (mul_nonneg ha.le (vectorNormSq_nonneg u)).trans hlo
  have hrel : a * (faceDot b u) ^ 2 ≤ faceDot b u :=
    (mul_le_mul_of_nonneg_left hcs ha.le).trans hlo
  change faceDot b u ≤ 1 / a
  apply (le_div_iff₀ ha).mpr
  by_cases hr : faceDot b u = 0
  · simp [hr]
  · have hrpos : 0 < faceDot b u := lt_of_le_of_ne hr0 (Ne.symm hr)
    nlinarith

namespace CompatibleFaceTuple

open FaceSmoother

variable {p q : ℕ} (S : CompatibleFaceTuple p q)

theorem activeCoordinateScores_eq (i : Fin q) :
    (fun k => normalDot (S.face k) (coordinateDirection (S.face i).1)) =
      fun k => if k = i then faceSign (S.face i) else 0 := by
  classical
  funext k
  rw [normalDot_coordinate_eq]
  by_cases hki : k = i
  · simp [hki]
  · have hcoord : (S.face k).1 ≠ (S.face i).1 := fun h => hki (S.coordinate_injective h)
    simp [hki, hcoord]

theorem activeCoordinateScores_normSq (i : Fin q) :
    vectorNormSq (fun k => normalDot (S.face k) (coordinateDirection (S.face i).1)) = 1 := by
  rw [S.activeCoordinateScores_eq]
  simp [vectorNormSq, faceSign_sq]

theorem coordinateDual_normSq_le (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * vectorNormSq u ≤ matrixQuadratic (S.gram (A * A.transpose)) u)
    (i : Fin q) : vectorNormSq (S.coordinateDual A (S.face i).1) ≤ 1 / a := by
  change vectorNormSq (S.regressionMean A
    (fun k => normalDot (S.face k) (coordinateDirection (S.face i).1))) ≤ _
  rw [S.regressionMean_normSq A hd]
  exact inverse_quadratic_le_inv _ hd ha hlower _ (S.activeCoordinateScores_normSq i).le

theorem coordinateDual_norm_le (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * vectorNormSq u ≤ matrixQuadratic (S.gram (A * A.transpose)) u)
    (i : Fin q) : ‖projectionEuclideanVector (S.coordinateDual A (S.face i).1)‖ ≤
      1 / Real.sqrt a := by
  have hn : ‖projectionEuclideanVector (S.coordinateDual A (S.face i).1)‖ ^ 2 =
      vectorNormSq (S.coordinateDual A (S.face i).1) := by
    simpa [projectionEuclideanVector, vectorNormSq, Real.norm_eq_abs, sq_abs] using
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin p => ℝ)
        (projectionEuclideanVector (S.coordinateDual A (S.face i).1))
  have hh := Real.sqrt_le_sqrt (S.coordinateDual_normSq_le A hd ha hlower i)
  rw [← hn, Real.sqrt_sq (norm_nonneg _), Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_one] at hh
  exact hh

/-- Every local dual linear factor is controlled by the actual projection
radius, with its Euclidean norm kept explicit for the refined Schur bound. -/
theorem abs_faceDot_coordinateDual_le (A : Matrix (Fin p) (Fin p) ℝ)
    (hq0 : 0 < q) (hq : q ≤ 4) (j : Fin p) (z : Vector p) :
    |faceDot (S.coordinateDual A j) z| ≤
      ‖projectionEuclideanVector (S.coordinateDual A j)‖ * fourFaceProjectionRadius A z := by
  let u : S.normalSpan A := ⟨projectionEuclideanVector (S.coordinateDual A j),
    S.regressionMean_mem_normalSpan A _⟩
  have hinner : faceDot (S.coordinateDual A j) z =
      ⟪u, (S.normalSpan A).orthogonalProjection (projectionEuclideanVector z)⟫_ℝ := by
    rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]
    simp [u, faceDot, projectionEuclideanVector, PiLp.inner_apply, mul_comm]
  rw [hinner]
  exact (abs_real_inner_le_norm u _).trans (mul_le_mul_of_nonneg_left
    (smallFaceSpan_projection_norm_le A S.face hq0 hq z) (norm_nonneg _))

theorem abs_faceDot_coordinateDual_le_inv_sqrt (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * vectorNormSq u ≤ matrixQuadratic (S.gram (A * A.transpose)) u)
    (hq0 : 0 < q) (hq : q ≤ 4) (i : Fin q) (z : Vector p) :
    |faceDot (S.coordinateDual A (S.face i).1) z| ≤
      (1 / Real.sqrt a) * fourFaceProjectionRadius A z :=
  (S.abs_faceDot_coordinateDual_le A hq0 hq _ z).trans
    (mul_le_mul_of_nonneg_right (S.coordinateDual_norm_le A hd ha hlower i)
      (fourFaceProjectionRadius_nonneg A z))

theorem gram_pair_lower (S : CompatibleFaceTuple p 2)
    {Q : Matrix (Fin p) (Fin p) ℝ}
    (hsym : ∀ j k, Q j k = Q k j) (hdiag : ∀ j, Q j j = 1) (u : Fin 2 → ℝ) :
    pairGap Q * vectorNormSq u ≤ matrixQuadratic (S.gram Q) u := by
  let ρ := S.gram Q 0 1
  have hρ : |ρ| ≤ 1 - pairGap Q := S.abs_gram_offDiagonal 0 1 (by decide)
  have h00 : S.gram Q 0 0 = 1 := S.gram_diagonal hdiag 0
  have h11 : S.gram Q 1 1 = 1 := S.gram_diagonal hdiag 1
  have h10 : S.gram Q 1 0 = ρ := S.gram_symmetric hsym 1 0
  have hnorm : vectorNormSq u = u 0 ^ 2 + u 1 ^ 2 := by
    simp [vectorNormSq, Fin.sum_univ_two]
  have hquad : matrixQuadratic (S.gram Q) u =
      u 0 ^ 2 + 2 * ρ * u 0 * u 1 + u 1 ^ 2 := by
    simp only [matrixQuadratic, Fin.sum_univ_two, h00, h11, h10]
    dsimp [ρ]
    ring
  have hproduct : 2 * |u 0 * u 1| ≤ u 0 ^ 2 + u 1 ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|u 0| - |u 1|), sq_abs (u 0), sq_abs (u 1)]
  have hcross : |2 * ρ * u 0 * u 1| ≤
      (1 - pairGap Q) * (u 0 ^ 2 + u 1 ^ 2) := by
    calc
      _ = |ρ| * (2 * |u 0 * u 1|) := by simp [abs_mul]; ring
      _ ≤ _ := mul_le_mul hρ hproduct (by positivity)
        (sub_nonneg.mpr (pairGap_le_one Q))
  rw [hnorm, hquad]
  nlinarith [neg_abs_le (2 * ρ * u 0 * u 1)]

theorem pair_coordinateDual_norm_le (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 2) :
    ‖projectionEuclideanVector (S.coordinateDual A (S.face i).1)‖ ≤
      1 / Real.sqrt (pairGap (A * A.transpose)) := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet : 0 < (S.gram (A * A.transpose)).det :=
    hc.trans_le (S.gram_two_det_ge_pairGap hsym hdiag hc.le)
  exact S.coordinateDual_norm_le A (isUnit_iff_ne_zero.mpr hdet.ne') hc
    (S.gram_pair_lower hsym hdiag) i

theorem pair_abs_faceDot_coordinateDual_le (S : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 2) (z : Vector p) :
    |faceDot (S.coordinateDual A (S.face i).1) z| ≤
      (1 / Real.sqrt (pairGap (A * A.transpose))) * fourFaceProjectionRadius A z :=
  (S.abs_faceDot_coordinateDual_le A (by decide) (by decide) _ z).trans
    (mul_le_mul_of_nonneg_right (S.pair_coordinateDual_norm_le A hdiag hc i)
      (fourFaceProjectionRadius_nonneg A z))

theorem singleton_coordinateDual_norm_le_one (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (i : Fin 1) : ‖projectionEuclideanVector (S.coordinateDual A (S.face i).1)‖ ≤ 1 := by
  have hG : S.gram (A * A.transpose) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext j k
    have hjk : j = k := Subsingleton.elim _ _
    subst k
    simpa using S.gram_diagonal hdiag j
  have hd : IsUnit (S.gram (A * A.transpose)).det := by rw [hG, Matrix.det_one]; exact isUnit_one
  have hlower : ∀ u, (1 : ℝ) * vectorNormSq u ≤
      matrixQuadratic (S.gram (A * A.transpose)) u := by
    intro u
    rw [hG]
    simp [matrixQuadratic, vectorNormSq, Fin.sum_univ_succ]
    ring_nf
    exact le_rfl
  simpa using S.coordinateDual_norm_le A hd (by norm_num : (0 : ℝ) < 1) hlower i

/-- Regression of a prospective face normal onto the active normal span. -/
def regressionCoefficients (A : Matrix (Fin p) (Fin p) ℝ) (f : Face p) : Fin q → ℝ :=
  (S.gram (A * A.transpose))⁻¹.mulVec (S.activeScores A (signedRowNormal A f))

theorem coordinateDual_newFace_coefficient (A : Matrix (Fin p) (Fin p) ℝ)
    (i : Fin q) (f : Face p) :
    normalDot f (A.mulVec (S.coordinateDual A (S.face i).1)) =
      faceSign (S.face i) * S.regressionCoefficients A f i := by
  have hsymQ : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  let G := S.gram (A * A.transpose)
  have hGt : G.transpose = G := by
    ext j k
    exact S.gram_symmetric hsymQ k j
  have hIt : G⁻¹.transpose = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hGt]
  have hIsym (j k : Fin q) : G⁻¹ j k = G⁻¹ k j := congrArg (fun M => M k j) hIt
  have hadjoint (b c : Fin q → ℝ) : faceDot (G⁻¹.mulVec b) c =
      faceDot b (G⁻¹.mulVec c) := by
    simp only [faceDot, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hIsym]
    ring
  rw [← faceDot_signedRowNormal_eq, faceDot_comm]
  unfold coordinateDual regressionMean
  rw [S.normalCombination_dot]
  rw [hadjoint]
  rw [S.activeCoordinateScores_eq]
  simp [faceDot, regressionCoefficients, G]

theorem abs_coordinateDual_newFace_coefficient_le (A : Matrix (Fin p) (Fin p) ℝ)
    (i : Fin q) (f : Face p) :
    |normalDot f (A.mulVec (S.coordinateDual A (S.face i).1))| ≤
      Real.sqrt (vectorNormSq (S.regressionCoefficients A f)) := by
  rw [S.coordinateDual_newFace_coefficient, abs_mul, abs_faceSign, one_mul]
  have hh : (S.regressionCoefficients A f i) ^ 2 ≤
      vectorNormSq (S.regressionCoefficients A f) :=
    Finset.single_le_sum (fun j _ => sq_nonneg (S.regressionCoefficients A f j))
      (Finset.mem_univ i)
  have h := Real.sqrt_le_sqrt hh
  simpa only [Real.sqrt_sq_eq_abs] using h

theorem triple_initial_regressionCoefficients (T : CompatibleFaceTuple p 3)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    T.initial.regressionCoefficients A (T.face 2) =
      ![GaussianTriple.regressionFirst (T.gram (A * A.transpose) 0 1)
          (T.gram (A * A.transpose) 0 2) (T.gram (A * A.transpose) 1 2),
        GaussianTriple.regressionSecond (T.gram (A * A.transpose) 0 1)
          (T.gram (A * A.transpose) 0 2) (T.gram (A * A.transpose) 1 2)] := by
  let Q := A * A.transpose
  let ρ := T.gram Q 0 1
  let α := T.gram Q 0 2
  let β := T.gram Q 1 2
  have hsym : ∀ j k, Q j k = Q k j := by
    intro j k
    simp only [Q, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hscalar : 0 < GaussianTriple.pairDeterminant ρ := hc.trans_le
    (GaussianTriple.pairDeterminant_lower hc.le (pairGap_le_one Q)
      (T.abs_gram_offDiagonal 0 1 (by decide)))
  have hd : IsUnit (T.initial.gram Q).det := isUnit_iff_ne_zero.mpr
    (ne_of_gt (hc.trans_le (T.initial.gram_two_det_ge_pairGap hsym hdiag hc.le)))
  have h00 : T.initial.gram Q 0 0 = 1 := T.initial.gram_diagonal hdiag 0
  have h11 : T.initial.gram Q 1 1 = 1 := T.initial.gram_diagonal hdiag 1
  have ht00 : T.gram Q 0 0 = 1 := T.gram_diagonal hdiag 0
  have ht11 : T.gram Q 1 1 = 1 := T.gram_diagonal hdiag 1
  have h01 : T.initial.gram Q 0 1 = ρ := rfl
  have h10 : T.initial.gram Q 1 0 = ρ := (T.initial.gram_symmetric hsym 1 0).trans h01
  have hr (i : Fin 2) : T.initial.activeScores A (signedRowNormal A (T.face 2)) i =
      T.gram Q i.castSucc 2 := by
    exact signedRowNormal_gram A (T.face i.castSucc) (T.face 2)
  let v : Fin 2 → ℝ := ![GaussianTriple.regressionFirst ρ α β,
    GaussianTriple.regressionSecond ρ α β]
  have hsolve : (T.initial.gram Q).mulVec v =
      T.initial.activeScores A (signedRowNormal A (T.face 2)) := by
    obtain ⟨heq0, heq1⟩ := GaussianTriple.regression_equations (α := α) (β := β) hscalar.ne'
    ext i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, v, h00, h01, hr, α, β, ρ,
        ht00, ht11] using heq0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, v, h10, h11, hr, α, β, ρ,
        ht00, ht11, T.gram_symmetric hsym 1 0] using heq1
  change (T.initial.gram Q)⁻¹.mulVec
    (T.initial.activeScores A (signedRowNormal A (T.face 2))) = v
  rw [← hsolve, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

theorem triple_initial_regression_weight_div_det_le (T : CompatibleFaceTuple p 3)
    (A : Matrix (Fin p) (Fin p) ℝ) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (1 + Real.sqrt (vectorNormSq (T.initial.regressionCoefficients A (T.face 2)))) /
      (T.gram (A * A.transpose)).det ≤ 2 / (a * pairGap (A * A.transpose)) := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [T.triple_initial_regressionCoefficients A hdiag hc]
  simpa only [vectorNormSq, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, GaussianTriple.regressionNormSq] using
    T.triple_regression_weight_div_det_le hQ ha hsym hdiag hc

/-- The actual coefficient created by the sparse dual-normal recursion,
combined with the final triple determinant. This retains exactly `a*c`. -/
theorem triple_initial_dualCoefficient_weight_div_det_le (T : CompatibleFaceTuple p 3)
    (A : Matrix (Fin p) (Fin p) ℝ) {a : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 2) :
    (1 + |normalDot (T.face 2)
      (A.mulVec (T.initial.coordinateDual A (T.initial.face i).1))|) /
      (T.gram (A * A.transpose)).det ≤ 2 / (a * pairGap (A * A.transpose)) := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet := T.gram_det_pos hQ ha hsym
  exact (div_le_div_of_nonneg_right (add_le_add_left
    (T.initial.abs_coordinateDual_newFace_coefficient_le A i (T.face 2)) 1) hdet.le).trans
    (T.triple_initial_regression_weight_div_det_le A hQ ha hdiag hc)

theorem singleton_abs_faceDot_coordinateDual_le (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (i : Fin 1) (z : Vector p) :
    |faceDot (S.coordinateDual A (S.face i).1) z| ≤ fourFaceProjectionRadius A z := by
  exact (S.abs_faceDot_coordinateDual_le A (by decide) (by decide) _ z).trans
    ((mul_le_mul_of_nonneg_right (S.singleton_coordinateDual_norm_le_one A hdiag i)
      (fourFaceProjectionRadius_nonneg A z)).trans_eq (one_mul _))

theorem singleton_abs_coordinateDual_hermite_le (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (i : Fin 1) (z : Vector p) :
    |faceDot (S.coordinateDual A (S.face i).1) z ^ 2 -
      faceDot (S.coordinateDual A (S.face i).1) (S.coordinateDual A (S.face i).1)| ≤
      fourFaceProjectionRadius A z ^ 2 + 1 := by
  have hdot := S.singleton_abs_faceDot_coordinateDual_le A hdiag i z
  have hnorm := S.singleton_coordinateDual_norm_le_one A hdiag i
  have hnormsq : faceDot (S.coordinateDual A (S.face i).1) (S.coordinateDual A (S.face i).1) =
      ‖projectionEuclideanVector (S.coordinateDual A (S.face i).1)‖ ^ 2 := by
    symm
    simpa [projectionEuclideanVector, faceDot, Real.norm_eq_abs, sq_abs, pow_two] using
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin p => ℝ)
        (projectionEuclideanVector (S.coordinateDual A (S.face i).1))
  have hsq : faceDot (S.coordinateDual A (S.face i).1) z ^ 2 ≤
      fourFaceProjectionRadius A z ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (fourFaceProjectionRadius_nonneg A z)).mpr hdot
    simpa only [sq_abs] using h
  calc
    _ ≤ |faceDot (S.coordinateDual A (S.face i).1) z ^ 2| +
        |faceDot (S.coordinateDual A (S.face i).1) (S.coordinateDual A (S.face i).1)| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (sq_nonneg _), hnormsq, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (projectionEuclideanVector (S.coordinateDual A (S.face i).1))]

theorem initial_regressionCoefficients_eq_lastColumn {r : ℕ}
    (T : CompatibleFaceTuple p (r + 1)) (A : Matrix (Fin p) (Fin p) ℝ) :
    T.initial.regressionCoefficients A (T.face (Fin.last r)) =
      ((T.gram (A * A.transpose)).submatrix Fin.castSucc Fin.castSucc)⁻¹.mulVec
        (fun i => T.gram (A * A.transpose) i.castSucc (Fin.last r)) := by
  unfold regressionCoefficients
  rw [T.initial_gram]
  apply congrArg (((T.gram (A * A.transpose)).submatrix Fin.castSucc Fin.castSucc)⁻¹.mulVec)
  funext i
  exact signedRowNormal_gram A (T.face i.castSucc) (T.face (Fin.last r))

/-- A refined Schur estimate for actual new-face regression coefficients.
The regression norm remains attached to the new determinant factor. -/
theorem initial_regression_weight_div_det_le {r : ℕ}
    (T : CompatibleFaceTuple p (r + 1)) (A : Matrix (Fin p) (Fin p) ℝ)
    {a : ℝ} (hQ : LocalCovarianceLower (A * A.transpose) (r + 1) a) (ha : 0 < a) :
    (1 + Real.sqrt (vectorNormSq (T.initial.regressionCoefficients A (T.face (Fin.last r))))) /
      (T.gram (A * A.transpose)).det ≤
        2 / (a * (T.initial.gram (A * A.transpose)).det) := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hlead := T.initial.gram_det_pos (hQ.mono (Nat.le_succ r)) ha hsym
  have hdet := T.gram_det_pos hQ ha hsym
  have hstrong := det_succ_ge_mul_leading_det_regression (T.gram (A * A.transpose))
    (T.gram_symmetric hsym) hlead (T.gram_lower hQ)
  have hs : a * (1 + vectorNormSq (T.initial.regressionCoefficients A (T.face (Fin.last r)))) *
      (T.initial.gram (A * A.transpose)).det ≤ (T.gram (A * A.transpose)).det := by
    simpa only [T.initial_regressionCoefficients_eq_lastColumn, T.initial_gram] using hstrong
  have hN := vectorNormSq_nonneg (T.initial.regressionCoefficients A (T.face (Fin.last r)))
  have hroot : 1 + Real.sqrt (vectorNormSq (T.initial.regressionCoefficients A (T.face (Fin.last r)))) ≤
      2 * (1 + vectorNormSq (T.initial.regressionCoefficients A (T.face (Fin.last r)))) := by
    nlinarith [Real.sq_sqrt hN,
      sq_nonneg (Real.sqrt (vectorNormSq (T.initial.regressionCoefficients A (T.face (Fin.last r)))) - 1)]
  apply (div_le_div_iff₀ hdet (mul_pos ha hlead)).mpr
  calc
    _ ≤ (2 * (1 + vectorNormSq
        (T.initial.regressionCoefficients A (T.face (Fin.last r))))) *
        (a * (T.initial.gram (A * A.transpose)).det) :=
      mul_le_mul_of_nonneg_right hroot (mul_nonneg ha.le hlead.le)
    _ = 2 * (a * (1 + vectorNormSq
        (T.initial.regressionCoefficients A (T.face (Fin.last r))))) *
        (T.initial.gram (A * A.transpose)).det := by ring
    _ ≤ _ := by linarith

/-- The nested pair--triple--quadruple coefficient cost has the exact local
scaling used by the fourth-order theorem. The full covariance may be singular. -/
theorem quadruple_nested_regression_weight_div_det_le (T : CompatibleFaceTuple p 4)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ}
    (hQ3 : LocalCovarianceLower (A * A.transpose) 3 a₃) (ha3 : 0 < a₃)
    (hQ4 : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha4 : 0 < a₄)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    ((1 + Real.sqrt (vectorNormSq (T.initial.initial.regressionCoefficients A (T.initial.face 2)))) *
      (1 + Real.sqrt (vectorNormSq (T.initial.regressionCoefficients A (T.face 3))))) /
      (T.gram (A * A.transpose)).det ≤
      4 / (pairGap (A * A.transpose) * a₃ * a₄) := by
  have hquad := T.initial_regression_weight_div_det_le A hQ4 ha4
  have htriple := T.initial.triple_initial_regression_weight_div_det_le A hQ3 ha3 hdiag hc
  have hN : 0 ≤ 1 + Real.sqrt (vectorNormSq
      (T.initial.initial.regressionCoefficients A (T.initial.face 2))) := by positivity
  calc
    _ = (1 + Real.sqrt (vectorNormSq
        (T.initial.initial.regressionCoefficients A (T.initial.face 2)))) *
        ((1 + Real.sqrt (vectorNormSq (T.initial.regressionCoefficients A (T.face 3))))) /
          (T.gram (A * A.transpose)).det := rfl
    _ ≤ (1 + Real.sqrt (vectorNormSq
        (T.initial.initial.regressionCoefficients A (T.initial.face 2)))) *
        (2 / (a₄ * (T.initial.gram (A * A.transpose)).det)) := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hquad hN
    _ = (2 / a₄) * ((1 + Real.sqrt (vectorNormSq
        (T.initial.initial.regressionCoefficients A (T.initial.face 2))))) /
          (T.initial.gram (A * A.transpose)).det := by ring
    _ ≤ (2 / a₄) * (2 / (a₃ * pairGap (A * A.transpose))) := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left htriple
        (div_nonneg (by norm_num) ha4.le)
    _ = _ := by field_simp; ring

theorem pair_inverse_sqrt_weight_div_det_le (T : CompatibleFaceTuple p 2)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) {a : ℝ} (ha : 0 < a)
    (hac : a ≤ pairGap (A * A.transpose)) :
    (1 / Real.sqrt (pairGap (A * A.transpose))) /
      (T.gram (A * A.transpose)).det ≤ 1 / (pairGap (A * A.transpose) * a) := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet := T.gram_two_det_ge_pairGap hsym hdiag hc.le
  have hc1 := pairGap_le_one (A * A.transpose)
  have hs := Real.sqrt_nonneg (pairGap (A * A.transpose))
  have hsq := Real.sq_sqrt hc.le
  have hcroot : pairGap (A * A.transpose) ≤ Real.sqrt (pairGap (A * A.transpose)) := by
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hc1)]
  rw [div_div]
  apply one_div_le_one_div_of_le (mul_pos hc ha)
  calc
    pairGap (A * A.transpose) * a ≤
        (T.gram (A * A.transpose)).det * Real.sqrt (pairGap (A * A.transpose)) :=
      mul_le_mul hdet (hac.trans hcroot) ha.le (hc.trans_le hdet).le
    _ = _ := mul_comm _ _

theorem singleton_abs_newFace_coefficient_le_one (T : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (i : Fin 1) (f : Face p) :
    |normalDot f (A.mulVec (T.coordinateDual A (T.face i).1))| ≤ 1 := by
  have hrow : ‖projectionEuclideanVector (signedRowNormal A f)‖ = 1 := by
    have hnorm : ‖projectionEuclideanVector (signedRowNormal A f)‖ ^ 2 =
        ∑ j, signedRowNormal A f j ^ 2 := by
      simpa [projectionEuclideanVector, Real.norm_eq_abs, sq_abs] using
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin p => ℝ)
          (projectionEuclideanVector (signedRowNormal A f))
    have hsum : (∑ j, signedRowNormal A f j ^ 2) = 1 := by
      calc
        _ = faceSign f ^ 2 * ∑ j, A f.1 j ^ 2 := by
          simp only [signedRowNormal, mul_pow, Finset.mul_sum]
        _ = (A * A.transpose) f.1 f.1 := by
          rw [faceSign_sq, one_mul]
          simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
        _ = 1 := hdiag f.1
    rw [hsum] at hnorm
    nlinarith [norm_nonneg (projectionEuclideanVector (signedRowNormal A f))]
  rw [← faceDot_signedRowNormal_eq]
  have heq : faceDot (signedRowNormal A f) (T.coordinateDual A (T.face i).1) =
      ⟪projectionEuclideanVector (signedRowNormal A f),
        projectionEuclideanVector (T.coordinateDual A (T.face i).1)⟫_ℝ := by
    simp [faceDot, projectionEuclideanVector, PiLp.inner_apply, mul_comm]
  rw [heq]
  exact (abs_real_inner_le_norm _ _).trans (by
    rw [hrow, one_mul]
    exact T.singleton_coordinateDual_norm_le_one A hdiag i)

end CompatibleFaceTuple
end
end RectangleCLT

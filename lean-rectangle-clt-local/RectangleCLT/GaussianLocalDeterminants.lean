import RectangleCLT.GaussianTriple
import RectangleCLT.LocalStatement
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Local spectral bounds for compatible signed active Gram determinants.
The successive Schur-complement factors preserve the separate pair, triple,
and four-coordinate covariance parameters. -/

open scoped BigOperators

namespace RectangleCLT

noncomputable section

private theorem matrixQuadratic_eq_dot {q : ℕ}
    (G : Matrix (Fin q) (Fin q) ℝ) (x : Fin q → ℝ) :
    matrixQuadratic G x = dotProduct x (G.mulVec x) := by
  simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- A positive local spectral lower bound gives a positive Gram determinant,
even when the full covariance matrix is singular. -/
theorem CompatibleFaceTuple.gram_det_pos {p q : ℕ}
    (S : CompatibleFaceTuple p q) {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (hQ : LocalCovarianceLower Q q a) (ha : 0 < a)
    (hsym : ∀ i j, Q i j = Q j i) : 0 < (S.gram Q).det := by
  have hpos : (S.gram Q).PosDef := by
    constructor
    · ext i j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using S.gram_symmetric hsym j i
    · intro x hx
      have hh := (mul_pos ha (vectorNormSq_pos hx)).trans_le (S.gram_lower hQ x)
      simpa only [matrixQuadratic_eq_dot, star_trivial] using hh
  exact hpos.det_pos

/-- The Schur test vector retains its full regression norm in the determinant
lower bound, without an additional inverse local-eigenvalue cost. -/
theorem det_succ_ge_mul_leading_det_regression {q : ℕ}
    (G : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) {a : ℝ}
    (hsym : ∀ i j, G i j = G j i)
    (hdet : 0 < (G.submatrix Fin.castSucc Fin.castSucc).det)
    (hlower : ∀ x, a * vectorNormSq x ≤ matrixQuadratic G x) :
    a * (1 + vectorNormSq ((G.submatrix Fin.castSucc Fin.castSucc)⁻¹.mulVec
      (fun i => G i.castSucc (Fin.last q)))) *
        (G.submatrix Fin.castSucc Fin.castSucc).det ≤ G.det := by
  classical
  let A := G.submatrix Fin.castSucc Fin.castSucc
  let u : Fin q → ℝ := fun i => G i.castSucc (Fin.last q)
  let β : Fin q → ℝ := A⁻¹.mulVec u
  let c := G (Fin.last q) (Fin.last q)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hdet)
  letI := Matrix.invertibleOfIsUnitDet A hunit
  have hAβ : A.mulVec β = u := by
    dsimp only [β]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  let x : Fin (q + 1) → ℝ := Fin.snoc (fun i => -β i) 1
  have hx (i : Fin q) : x i.castSucc = -β i := Fin.snoc_castSucc _ _ i
  have hxlast : x (Fin.last q) = 1 := Fin.snoc_last _ _
  have hrow (i : Fin q) : G.mulVec x i.castSucc = 0 := by
    have hh := congrFun hAβ i
    simp only [Matrix.mulVec, dotProduct, A, Matrix.submatrix_apply, u] at hh
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hx, hxlast, mul_one]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
    linarith
  have hlast : G.mulVec x (Fin.last q) = c - dotProduct u β := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hx, hxlast, mul_one]
    simp_rw [hsym (Fin.last q), mul_neg]
    rw [Finset.sum_neg_distrib]
    dsimp [c, u]
    ring
  have hquad : matrixQuadratic G x = c - dotProduct u β := by
    rw [matrixQuadratic_eq_dot]
    simp only [dotProduct, Fin.sum_univ_castSucc, hx, hxlast, hrow, hlast, mul_zero,
      Finset.sum_const_zero, one_mul, zero_add]
  have hnorm : vectorNormSq x = vectorNormSq β + 1 := by
    simp [vectorNormSq, Fin.sum_univ_castSucc, hx, hxlast]
  have hschur : a * (1 + vectorNormSq β) ≤ c - dotProduct u β := by
    have hh := hlower x
    rw [hquad, hnorm] at hh
    simpa only [add_comm] using hh
  let B : Matrix (Fin q) (Fin 1) ℝ := fun i _ => u i
  let C : Matrix (Fin 1) (Fin q) ℝ := fun _ i => u i
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => c
  let e : Fin q ⊕ Fin 1 ≃ Fin (q + 1) := finSumFinEquiv
  have hblock : G.submatrix e e = Matrix.fromBlocks A B C D := by
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => rfl
      | inr j => fin_cases j; rfl
    | inr i => cases j with
      | inl j => fin_cases i; exact hsym _ _
      | inr j => fin_cases i; fin_cases j; rfl
  have hdeq : G.det = A.det * (c - dotProduct u β) := by
    rw [← Matrix.det_submatrix_equiv_self e, hblock, Matrix.det_fromBlocks₁₁,
      Matrix.invOf_eq_nonsing_inv]
    rw [Matrix.det_unique (D - C * A⁻¹ * B)]
    congr 1
    simp only [Matrix.sub_apply, D, C, B, Matrix.mul_apply, β,
      Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdeq]
  simpa only [A, β, u, mul_comm] using mul_le_mul_of_nonneg_left hschur hdet.le

/-- Adjoining one coordinate multiplies a positive leading determinant by at
least the local Rayleigh lower bound. -/
theorem det_succ_ge_mul_leading_det {q : ℕ}
    (G : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hsym : ∀ i j, G i j = G j i)
    (hdet : 0 < (G.submatrix Fin.castSucc Fin.castSucc).det)
    (hlower : ∀ x, a * vectorNormSq x ≤ matrixQuadratic G x) :
    a * (G.submatrix Fin.castSucc Fin.castSucc).det ≤ G.det := by
  have hstrong := det_succ_ge_mul_leading_det_regression G hsym hdet hlower
  have hn := vectorNormSq_nonneg ((G.submatrix Fin.castSucc Fin.castSucc)⁻¹.mulVec
    (fun i => G i.castSucc (Fin.last q)))
  have hle : a ≤ a * (1 + vectorNormSq ((G.submatrix Fin.castSucc Fin.castSucc)⁻¹.mulVec
      (fun i => G i.castSucc (Fin.last q)))) := by nlinarith
  exact (mul_le_mul_of_nonneg_right hle hdet.le).trans hstrong

namespace CompatibleFaceTuple

/-- The initial compatible subtuple obtained by discarding its last face. -/
def initial {p q : ℕ} (S : CompatibleFaceTuple p (q + 1)) : CompatibleFaceTuple p q where
  face i := S.face i.castSucc
  coordinate_injective := fun _ _ hij => Fin.ext (congrArg (fun k : Fin (q + 1) => k.val) (S.coordinate_injective hij))

@[simp] theorem initial_gram {p q : ℕ} (S : CompatibleFaceTuple p (q + 1))
    (Q : Matrix (Fin p) (Fin p) ℝ) :
    S.initial.gram Q = (S.gram Q).submatrix Fin.castSucc Fin.castSucc := rfl

/-- The compatible two-face Gram determinant costs only one pair gap. -/
theorem gram_two_det_ge_pairGap {p : ℕ} (S : CompatibleFaceTuple p 2)
    {Q : Matrix (Fin p) (Fin p) ℝ}
    (hsym : ∀ i j, Q i j = Q j i) (hdiag : ∀ j, Q j j = 1)
    (hc : 0 ≤ pairGap Q) : pairGap Q ≤ (S.gram Q).det := by
  have heq : (S.gram Q).det = GaussianTriple.pairDeterminant (S.gram Q 0 1) := by
    rw [Matrix.det_fin_two, S.gram_diagonal hdiag 0, S.gram_diagonal hdiag 1,
      S.gram_symmetric hsym 1 0]
    unfold GaussianTriple.pairDeterminant
    ring
  rw [heq]
  exact GaussianTriple.pairDeterminant_lower hc (pairGap_le_one Q)
    (S.abs_gram_offDiagonal 0 1 (by decide))

/-- A compatible triple has the refined determinant lower bound retaining
one pair-gap factor and one three-coordinate eigenvalue factor. -/
theorem gram_three_det_ge_pairGap_mul_a3 {p : ℕ} (S : CompatibleFaceTuple p 3)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : LocalCovarianceHypotheses Q) :
    pairGap Q * a3 Q ≤ (S.gram Q).det := by
  have hp : 0 < p := Nat.zero_lt_of_lt (S.face 0).1.isLt
  have hc := pairGap_pos_of_a4_pos hp hQ.posSemidef hQ.unit_diagonal hQ.a4_pos
  have ha3 := a3_pos_of_a4_pos hp hQ.posSemidef hQ.a4_pos
  have hsym := matrix_symmetric_of_posSemidef hQ.posSemidef
  have hpair := S.initial.gram_two_det_ge_pairGap hsym hQ.unit_diagonal hc.le
  have hpd : 0 < ((S.gram Q).submatrix Fin.castSucc Fin.castSucc).det := by
    simpa only [← S.initial_gram Q] using hc.trans_le hpair
  have hstep := det_succ_ge_mul_leading_det (S.gram Q) ha3.le
    (S.gram_symmetric hsym) hpd
    (S.gram_lower (localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hQ.posSemidef)))
  have hh := (mul_le_mul_of_nonneg_left hpair ha3.le).trans hstep
  simpa only [mul_comm, initial_gram] using hh

/-- The four-face Gram determinant preserves the manuscript's three distinct
local covariance factors, even when the full covariance is singular. -/
theorem gram_four_det_ge_pairGap_mul_a3_mul_a4 {p : ℕ} (S : CompatibleFaceTuple p 4)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : LocalCovarianceHypotheses Q) :
    pairGap Q * a3 Q * a4 Q ≤ (S.gram Q).det := by
  have hp : 0 < p := Nat.zero_lt_of_lt (S.face 0).1.isLt
  have hc := pairGap_pos_of_a4_pos hp hQ.posSemidef hQ.unit_diagonal hQ.a4_pos
  have ha3 := a3_pos_of_a4_pos hp hQ.posSemidef hQ.a4_pos
  have htriple := S.initial.gram_three_det_ge_pairGap_mul_a3 hQ
  have htd : 0 < ((S.gram Q).submatrix Fin.castSucc Fin.castSucc).det := by
    simpa only [← S.initial_gram Q] using (mul_pos hc ha3).trans_le htriple
  have hstep := det_succ_ge_mul_leading_det (S.gram Q) hQ.a4_pos.le
    (S.gram_symmetric (matrix_symmetric_of_posSemidef hQ.posSemidef)) htd
    (S.gram_lower (localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hQ.posSemidef)))
  have hh := (mul_le_mul_of_nonneg_left htriple hQ.a4_pos.le).trans hstep
  simpa only [mul_comm, initial_gram] using hh

/-- In particular every compatible active quadruple has invertible Gram
matrix under the actual local-covariance hypotheses. -/
theorem gram_four_det_isUnit {p : ℕ} (S : CompatibleFaceTuple p 4)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : LocalCovarianceHypotheses Q) :
    IsUnit (S.gram Q).det := by
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (S.gram_det_pos
    (localEigenvalue_lower (matrixQuadratic_nonneg_of_posSemidef hQ.posSemidef))
    hQ.a4_pos (matrix_symmetric_of_posSemidef hQ.posSemidef)))

end CompatibleFaceTuple

end

end RectangleCLT
